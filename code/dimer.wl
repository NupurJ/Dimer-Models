(* ::Package:: *)

(*make random dimer tilings in 2D and 3D using random flips*)


(*some grids and initial tilings (called bricks)*)
(*All tilings are sorted so that tiles go from white to black*)
whitetoblacksort[dimer_]:=If[EvenQ[Total[dimer[[1]]]],dimer,Reverse[dimer]]
(*1. rectangular*)
(*2D*)
grid2D[n_,m_]:=grid2D[n,m]=Flatten[Table[{a,b},{a,0,n-1},{b,0,m-1}],1]
bricks2D[n_,m_]:=bricks2D[n,m]=whitetoblacksort[#]&/@Partition[grid2D[n,m],2]
(*3D*)
grid3D[n_,m_,k_]:=grid3D[n,m,k]=Flatten[Table[{a,b,c},{a,0,n-1},{b,0,m-1},{c,0,k-1}],2];
bricks3D[n_,m_,k_]:=bricks3D[n,m,k]=whitetoblacksort[#]&/@Partition[grid3D[n,m,k],2]

(*2. variants of the aztec diamond*)
coordinator[{x_,list_}]:=Table[{x,list[[i]]},{i,1,Length[list]}]
(*2D aztec diamond*)
aztecgrid[k_]:=aztecgrid[k]=Catenate[Map[coordinator,Partition[Riffle[Table[i+1/2,{i,-k,k}],Join[Reverse[Table[Table[i-1/2,{i,-n+1,n}],{n,k,1,-1}]],Table[Table[i-1/2,{i,-n+1,n}],{n,k,1,-1}]]],2]]]
aztecbricks[k_]:=aztecbricks[k]=Partition[aztecgrid[k],2]
(*aztec prism, e.g. aztec diamond crossed with an interval*)
aztecprism[k_,n_]:=aztecprism[k,n]=Flatten[#,1]&/@SortBy[Catenate[Table[{aztecgrid[k][[i]],j},{i,1,Length[aztecgrid[k]]},{j,1,n}]],Last]
aztecprismbricks[k_,n_]:=aztecprismbricks[k,n]=Partition[aztecprism[k,n],2]
(*octahedron*)
aztechedron[k_]:=aztechedron[k]=Catenate[Join[Table[Append[#,k-m+1/2]&/@aztecgrid[Abs[m]],{m,0,k}],Table[Append[#,m-k-1+1/2]&/@aztecgrid[Abs[m]],{m,0,k}]]]
aztechedronbricks[k_]:=aztechedronbricks[k]=Partition[aztechedron[k],2]
(*aztec diamond pyramid/half octahedron*)
halfaztechedron[k_]:=halfaztechedron[k]=Catenate[Table[Append[#,k-m+1/2]&/@aztecgrid[Abs[m]],{m,0,k}]]
halfaztechedronbricks[k_]:=halfaztechedronbricks[k]=Partition[halfaztechedron[k],2]

(*3. stacked squares*)
(*square pyramid*)
squarepyramid[n_]:=squarepyramid[n]=Catenate[Table[PadRight[#,3,k-(k-2)/2]&/@Evaluate[({#[[1]]-k/2,#[[2]]-k/2})&/@grid2D[k,k]],{k,2,n,2}]]
squarepyramidbricks[n_]:=squarepyramidbricks[n]=Partition[squarepyramid[n],2]
(*square tower (1/4 of square pyramid)*)
squaretower[n_]:=Catenate[Table[PadRight[#,3,k-(k-2)/2]&/@grid2D[k,k],{k,2,n,2}]]
squaretowerbricks[n_]:=Partition[squaretower[n],2]



(*calculating the squares in a grid*)

square[point_,vec1_,vec2_]:={point,point+vec1,point+vec1+vec2,point+vec2}
squaregridcheck[grid_,square_]:=If[MemberQ[MemberQ[grid,#]&/@square,False],Nothing,square]
gridsquares3D[grid_]:=squaregridcheck[grid,#]&/@Catenate[{square[#,{1,0,0},{0,1,0}],square[#,{1,0,0},{0,0,1}],square[#,{0,1,0},{0,0,1}]}&/@grid]
gridsquares2D[grid_]:=squaregridcheck[grid,#]&/@Evaluate[square[#,{1,0},{0,1}]&/@grid]

(*checking if a square contains a pair of dominoes in the tiling*)

possiblepairs[square_]:=Union[Partition[Join[square,{First[square]}],2,1],Reverse[#]&/@Partition[Join[square,{First[square]}],2,1]]
squareparallels[tiling_,square_]:=Intersection[tiling,possiblepairs[square]]


(*flipping a given pair of dominoes*)

dominoflip2D[{{{a1_,a2_},{a4_,a5_}},{{b1_,b2_},{b4_,b5_}}}]:={{{a1,a2},{b1,b2}},{{a4,a5},{b4,b5}}}
dominoflip3D[{{{a1_,a2_,a3_},{a4_,a5_,a6_}},{{b1_,b2_,b3_},{b4_,b5_,b6_}}}]:={{{a1,a2,a3},{b1,b2,b3}},{{a4,a5,a6},{b4,b5,b6}}}

(*select one random square, and flip dominoes if possible, otherwise do nothing*)

randomflip3D[{squares_,tiling_}]:=Block[{choice,newtiles},	
choice=RandomChoice[squares];
newtiles=If[Length[squareparallels[tiling,choice]]==2,ReplaceAll[squareparallels[tiling,choice][[2]]->dominoflip3D[squareparallels[tiling,choice]][[2]]][ReplaceAll[squareparallels[tiling,choice][[1]]->dominoflip3D[squareparallels[tiling,choice]][[1]]][tiling]],tiling];
{squares,newtiles}]

randomflip2D[{squares_,tiling_}]:=Block[{choice,newtiles},	
choice=RandomChoice[squares];
newtiles=If[Length[squareparallels[tiling,choice]]==2,ReplaceAll[squareparallels[tiling,choice][[2]]->dominoflip2D[squareparallels[tiling,choice]][[2]]][ReplaceAll[squareparallels[tiling,choice][[1]]->dominoflip2D[squareparallels[tiling,choice]][[1]]][tiling]],tiling];
{squares,newtiles}]


(*various random tiling functions in 2D*)

(*random a 2D tiling with N flip-checks. All bricks are brickColor. Also displays time to calculate.*)
randomtiling2D[grid_,tiling_,N_]:=Timing[Block[{squares},squares=gridsquares2D[grid];
Graphics[{EdgeForm[{Thick,White}],brickColor,domino2D[#]}&/@Last[Nest[randomflip2D,{squares,tiling},N]]]]]

(*random 2D tiling with N flip-checks. Bricks are 4 different colors based on direction/parity. Also displays time to calculate*)
randomtiling2Dcolors[grid_,tiling_,N_]:=Timing[Block[{squares},squares=gridsquares2D[grid];
Graphics[{EdgeForm[{Thick,White}],fourcolor2D[#],domino2D[#]}&/@Last[Nest[randomflip2D,{squares,tiling},N]]]]]

(*random 2D tiling with N flip-checks. Makes graphic and output the final tiling and time to calculate*)
randomtiling2Dcolorsdata[grid_,tiling_,N_]:=Timing[Block[{squares,finaltiles},
squares=gridsquares2D[grid]; 
finaltiles=Last[Nest[randomflip2D,{squares,tiling},N]]; 
{Graphics[{EdgeForm[{Thick,White}],fourcolor2D[#],domino2D[#]}&/@finaltiles], finaltiles}]]


(*various random tiling functions in 3D*)

(*random 3D tiling with N flip-checks. All bricks are brickColor. Also displays time to calculate*)
randomtiling3D[grid_,tiling_,N_]:=Timing[Block[{squares},squares=gridsquares3D[grid];
Graphics3D[{EdgeForm[{Thick,White}],brickColor,Opacity[0.7],domino3D[#]}&/@Last[Nest[randomflip3D,{squares,tiling},N]]]]]

(*random 3D tiling with N flip-checks. Bricks are 6 different colors based on direction/parity. Also displays time to calculate.*)
randomtiling3Dcolors[grid_,tiling_,N_]:=Timing[Block[{squares},squares=gridsquares3D[grid];
Graphics3D[{EdgeForm[White],Opacity[0.7],sixcolor3D[#],domino3D[#]}&/@Last[Nest[randomflip3D,{squares,tiling},N]]]]]

(*random 3D tiling with N flip-check. Makes graphic and outputs the final tiling and time to calculate*)
randomtiling3Dcolorsdata[grid_,tiling_,N_]:=Timing[Block[{squares,finaltiles},
squares=gridsquares3D[grid];
finaltiles=Last[Nest[randomflip3D,{squares,tiling},N]];
{Graphics3D[{EdgeForm[White],Opacity[0.7],sixcolor3D[#],domino3D[#]}&/@finaltiles],finaltiles}]]

(*random 3D tiling with N flip-checks. Displays 3D graphic with 6 colors and 2D slices (at the heights listed) in z = const. planes*)
randomtiling3Dslices[grid_,tiling_,N_,min_,max_,spacing_]:=Timing[Block[{squares,randomtiling},
squares=gridsquares3D[grid];
randomtiling=Last[Nest[randomflip3D,{squares, tiling},N]];
{Graphics3D[{EdgeForm[White],Opacity[0.7],sixcolor3D[#],domino3D[#]}&/@randomtiling],
Table[Graphics[{EdgeForm[White],sixcolor3D[#],domino2D[clip3[#]]}&/@Select[randomtiling,Or[#[[2]][[3]]==i,#[[1]][[3]]==i]&]],{i,min,max,spacing}]}]]

randomtiling3Dallslices[grid_,tiling_,N_,{xmin_,xmax_,xspacing_},{ymin_,ymax_,yspacing_},{zmin_,zmax_,zspacing_}]:=Timing[Block[{squares,randomtiling},
squares=gridsquares3D[grid];
randomtiling=Last[Nest[randomflip3D,{squares, tiling},N]];
{Graphics3D[{EdgeForm[White],Opacity[0.7],sixcolor3D[#],domino3D[#]}&/@randomtiling],
Table[Graphics[{EdgeForm[White],sixcolor3D[#],domino2D[clip3[#]]}&/@Select[randomtiling,Or[#[[2]][[3]]==i,#[[1]][[3]]==i]&]],{i,zmin,zmax,zspacing}],
Table[Graphics[{EdgeForm[White],sixcolor3D[#],domino2D[clip2[#]]}&/@Select[randomtiling,Or[#[[2]][[2]]==i,#[[1]][[2]]==i]&]],{i,ymin,ymax,yspacing}],
Table[Graphics[{EdgeForm[White],sixcolor3D[#],domino2D[clip1[#]]}&/@Select[randomtiling,Or[#[[2]][[1]]==i,#[[1]][[1]]==i]&]],{i,xmin,xmax,xspacing}]}]]



(*graphics for dominoes*)
domino2D[{{a_,b_},{c_,d_}}]:=Rectangle[{Min[a,c]-1/2,Min[b,d]-1/2},{Max[a,c]+1/2,Max[b,d]+1/2}]
domino3D [{{a_,b_,c_},{d_,e_,f_}}]:=Cuboid[{Min[a,d]-1/2,Min[b,e]-1/2,Min[c,f]-1/2},{Max[a,d]+1/2,Max[b,e]+1/2,Max[c,f]+1/2}]
(*for making slices in 3D (clip cuts off the 3rd coordinate of the domino)*)
clip3[{{a_,b_,c_},{d_,e_,f_}}]:={{a,b},{d,e}}
clip1[{{a_,b_,c_},{d_,e_,f_}}]:={{b,c},{e,f}}
clip2[{{a_,b_,c_},{d_,e_,f_}}]:={{a,c},{d,f}}

(*color functions*)
brickColor=Hue[0.03,1,0.8];
fourcolor2D[{{a_,b_},{c_,d_}}]:=Which[a-c==0&&OddQ[Floor[Min[b,d]-Floor[a]]],Hue[5/6,1,1/2],a-c==0&&EvenQ[Floor[Min[b,d]-Floor[a]]],Hue[0.08,0.87,0.94],Abs[a-c]==1&&OddQ[Floor[Min[a,c]]-Floor[b]],Hue[0.56,0.65,0.93],Abs[a-c]==1&&EvenQ[Floor[Min[a,c]]-Floor[b]],Hue[0.29,0.88,0.87]]
sixcolor3D[{{a_,b_,c_},{d_,e_,f_}}]:=Which[a-d==0&&c-f==0&&Abs[b-e]==1&&OddQ[Floor[Min[b,e]]+Floor[a]+Floor[c]],Hue[5/6,1,1/2],a-d==0&&c-f==0&&Abs[b-e]==1&&EvenQ[Floor[Min[b,e]]+Floor[a]+Floor[c]],Hue[0.08,0.87,0.94],Abs[a-d]==1&&b-e==0&&c-f==0&&OddQ[Floor[Min[a,d]]+Floor[b]+Floor[c]],Hue[0.56,0.65,0.93],Abs[a-d]==1&&b-e==0&&c-f==0&&EvenQ[Floor[Min[a,d]]+Floor[b]+Floor[c]],Hue[0.29,0.88,0.87],a-d==0&&b-e==0&&Abs[c-f]==1&&OddQ[Floor[Min[c,f]]+Floor[a]+Floor[b]], Hue[0,0.97,0.94],a-d==0&&b-e==0&&Abs[c-f]==1&&EvenQ[Floor[Min[c,f]]+Floor[a]+Floor[b]],Hue[0.15,1,1]]

