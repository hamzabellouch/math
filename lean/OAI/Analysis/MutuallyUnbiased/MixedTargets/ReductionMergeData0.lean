import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData0
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData1

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge0 : Integer.Sparse Master := [(Sum.inl 0, 4526895990700081152000), (Sum.inl 1, -5071151322752901120000), (Sum.inl 2, -2721276660264099840000)]

def originalMerge0 : Integer.Sparse OriginalKey := originalTerm1 ++ originalTerm2

theorem reducedMerge0Check : reducedMerge0 = Integer.Sparse.mergeBy masterLess reducedTerm1 reducedTerm2 := by decide +kernel

def reducedMerge1 : Integer.Sparse Master := [(Sum.inl 0, 7090058769856634880000), (Sum.inl 1, -1575929351175782400000), (Sum.inl 2, -391128679212687360000)]

def originalMerge1 : Integer.Sparse OriginalKey := originalTerm0 ++ originalMerge0

theorem reducedMerge1Check : reducedMerge1 = Integer.Sparse.mergeBy masterLess reducedTerm0 reducedMerge0 := by decide +kernel

def reducedMerge2 : Integer.Sparse Master := [(Sum.inl 0, 9608550735739576320000), (Sum.inl 1, -2576043458403287040000), (Sum.inl 2, 1979338354864496640000)]

def originalMerge2 : Integer.Sparse OriginalKey := originalTerm3 ++ originalTerm4

theorem reducedMerge2Check : reducedMerge2 = Integer.Sparse.mergeBy masterLess reducedTerm3 reducedTerm4 := by decide +kernel

def reducedMerge3 : Integer.Sparse Master := [(Sum.inl 0, 3009387278866268160000), (Sum.inl 1, 4892413635164160000000)]

def originalMerge3 : Integer.Sparse OriginalKey := originalTerm5 ++ originalTerm6

theorem reducedMerge3Check : reducedMerge3 = Integer.Sparse.mergeBy masterLess reducedTerm5 reducedTerm6 := by decide +kernel

def reducedMerge4 : Integer.Sparse Master := [(Sum.inl 0, 12617938014605844480000), (Sum.inl 1, 2316370176760872960000), (Sum.inl 2, 1979338354864496640000)]

def originalMerge4 : Integer.Sparse OriginalKey := originalMerge2 ++ originalMerge3

theorem reducedMerge4Check : reducedMerge4 = Integer.Sparse.mergeBy masterLess reducedMerge2 reducedMerge3 := by decide +kernel

def reducedMerge5 : Integer.Sparse Master := [(Sum.inl 0, 19707996784462479360000), (Sum.inl 1, 740440825585090560000), (Sum.inl 2, 1588209675651809280000)]

def originalMerge5 : Integer.Sparse OriginalKey := originalMerge1 ++ originalMerge4

theorem reducedMerge5Check : reducedMerge5 = Integer.Sparse.mergeBy masterLess reducedMerge1 reducedMerge4 := by decide +kernel

def reducedMerge6 : Integer.Sparse Master := [(Sum.inl 1, 10094470660915200000), (Sum.inl 2, 22712558987059200000), (Sum.inl 5, -191794942557388800000), (Sum.inl 6, 50472353304576000000), (Sum.inl 7, 242267295861964800000), (Sum.inl 9, -161511530574643200000), (Sum.inl 35, 121133647930982400000), (Sum.inl 58, 7570852995686400000), (Sum.inl 69, 403778826436608000000), (Sum.inl 70, 363400943792947200000), (Sum.inl 71, 323023061149286400000), (Sum.inl 257, 80755765287321600000)]

def originalMerge6 : Integer.Sparse OriginalKey := originalTerm8 ++ originalTerm9

theorem reducedMerge6Check : reducedMerge6 = Integer.Sparse.mergeBy masterLess reducedTerm8 reducedTerm9 := by decide +kernel

def reducedMerge7 : Integer.Sparse Master := [(Sum.inl 0, 1737686641551114240000), (Sum.inl 1, 467380428963840000000), (Sum.inl 2, 22712558987059200000), (Sum.inl 5, -191794942557388800000), (Sum.inl 6, 50472353304576000000), (Sum.inl 7, 242267295861964800000), (Sum.inl 9, -161511530574643200000), (Sum.inl 35, 121133647930982400000), (Sum.inl 58, 7570852995686400000), (Sum.inl 69, 403778826436608000000), (Sum.inl 70, 363400943792947200000), (Sum.inl 71, 323023061149286400000), (Sum.inl 257, 80755765287321600000)]

def originalMerge7 : Integer.Sparse OriginalKey := originalTerm7 ++ originalMerge6

theorem reducedMerge7Check : reducedMerge7 = Integer.Sparse.mergeBy masterLess reducedTerm7 reducedMerge6 := by decide +kernel

def reducedMerge8 : Integer.Sparse Master := [(Sum.inl 0, 160183371938365440000), (Sum.inl 1, 39069115106918400000), (Sum.inl 2, 117207345320755200000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 625105841710694400000), (Sum.inl 7, -1875317525132083200000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 234414690641510400000), (Sum.inl 35, -1250211683421388800000), (Sum.inl 52, -312552920855347200000), (Sum.inl 58, 19534557553459200000), (Sum.inl 69, -1875317525132083200000), (Sum.inl 70, -1562764604276736000000), (Sum.inl 71, -1250211683421388800000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -625105841710694400000), (Sum.inl 495, -312552920855347200000)]

def originalMerge8 : Integer.Sparse OriginalKey := originalTerm10 ++ originalTerm11

theorem reducedMerge8Check : reducedMerge8 = Integer.Sparse.mergeBy masterLess reducedTerm10 reducedTerm11 := by decide +kernel

def reducedMerge9 : Integer.Sparse Master := [(Sum.inl 0, -85643809957601280000), (Sum.inl 1, 180952399595520000000), (Sum.inl 2, 75709144472371200000), (Sum.inl 5, 71961408781516800000), (Sum.inl 6, 46175033821593600000), (Sum.inl 7, -438163937132544000000), (Sum.inl 9, 80556867101491200000), (Sum.inl 35, -219081968566272000000), (Sum.inl 58, 34631275366195200000), (Sum.inl 69, -657245905698816000000), (Sum.inl 70, -657245905698816000000), (Sum.inl 71, -219081968566272000000), (Sum.inl 257, -219081968566272000000)]

def originalMerge9 : Integer.Sparse OriginalKey := originalTerm12 ++ originalTerm13

theorem reducedMerge9Check : reducedMerge9 = Integer.Sparse.mergeBy masterLess reducedTerm12 reducedTerm13 := by decide +kernel

def reducedMerge10 : Integer.Sparse Master := [(Sum.inl 0, 74539561980764160000), (Sum.inl 1, 220021514702438400000), (Sum.inl 2, 192916489793126400000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 697067250492211200000), (Sum.inl 6, 46175033821593600000), (Sum.inl 7, -2313481462264627200000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 314971557743001600000), (Sum.inl 35, -1469293651987660800000), (Sum.inl 52, -312552920855347200000), (Sum.inl 58, 54165832919654400000), (Sum.inl 69, -2532563430830899200000), (Sum.inl 70, -2220010509975552000000), (Sum.inl 71, -1469293651987660800000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -844187810276966400000), (Sum.inl 495, -312552920855347200000)]

def originalMerge10 : Integer.Sparse OriginalKey := originalMerge8 ++ originalMerge9

theorem reducedMerge10Check : reducedMerge10 = Integer.Sparse.mergeBy masterLess reducedMerge8 reducedMerge9 := by decide +kernel

def reducedMerge11 : Integer.Sparse Master := [(Sum.inl 0, 1812226203531878400000), (Sum.inl 1, 687401943666278400000), (Sum.inl 2, 215629048780185600000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 505272307934822400000), (Sum.inl 6, 96647387126169600000), (Sum.inl 7, -2071214166402662400000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 153460027168358400000), (Sum.inl 35, -1348160004056678400000), (Sum.inl 52, -312552920855347200000), (Sum.inl 58, 61736685915340800000), (Sum.inl 69, -2128784604394291200000), (Sum.inl 70, -1856609566182604800000), (Sum.inl 71, -1146270590838374400000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -763432044989644800000), (Sum.inl 495, -312552920855347200000)]

def originalMerge11 : Integer.Sparse OriginalKey := originalMerge7 ++ originalMerge10

theorem reducedMerge11Check : reducedMerge11 = Integer.Sparse.mergeBy masterLess reducedMerge7 reducedMerge10 := by decide +kernel

def reducedMerge12 : Integer.Sparse Master := [(Sum.inl 0, 21520222987994357760000), (Sum.inl 1, 1427842769251368960000), (Sum.inl 2, 1803838724431994880000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 505272307934822400000), (Sum.inl 6, 96647387126169600000), (Sum.inl 7, -2071214166402662400000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 153460027168358400000), (Sum.inl 35, -1348160004056678400000), (Sum.inl 52, -312552920855347200000), (Sum.inl 58, 61736685915340800000), (Sum.inl 69, -2128784604394291200000), (Sum.inl 70, -1856609566182604800000), (Sum.inl 71, -1146270590838374400000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -763432044989644800000), (Sum.inl 495, -312552920855347200000)]

def originalMerge12 : Integer.Sparse OriginalKey := originalMerge5 ++ originalMerge11

theorem reducedMerge12Check : reducedMerge12 = Integer.Sparse.mergeBy masterLess reducedMerge5 reducedMerge11 := by decide +kernel

def reducedMerge13 : Integer.Sparse Master := [(Sum.inl 0, -26025529345966080000), (Sum.inl 1, -58603672660377600000), (Sum.inl 2, -184117085481369600000), (Sum.inl 5, 329165055855820800000), (Sum.inl 6, -94750365214310400000), (Sum.inl 7, -312552920855347200000), (Sum.inl 8, -312552920855347200000), (Sum.inl 9, 502053651283968000000), (Sum.inl 58, -71062773910732800000), (Sum.inl 69, -625105841710694400000), (Sum.inl 70, -312552920855347200000), (Sum.inl 71, -937658762566041600000), (Sum.inl 256, 937658762566041600000), (Sum.inl 495, -379001460857241600000)]

def originalMerge13 : Integer.Sparse OriginalKey := originalTerm15 ++ originalTerm16

theorem reducedMerge13Check : reducedMerge13 = Integer.Sparse.mergeBy masterLess reducedTerm15 reducedTerm16 := by decide +kernel

def reducedMerge14 : Integer.Sparse Master := [(Sum.inl 0, -78138230213836800000), (Sum.inl 1, -70447468312166400000), (Sum.inl 2, -172273289829580800000), (Sum.inl 5, 423915421070131200000), (Sum.inl 6, -165813139125043200000), (Sum.inl 7, -312552920855347200000), (Sum.inl 8, -312552920855347200000), (Sum.inl 9, 691554381712588800000), (Sum.inl 35, -379001460857241600000), (Sum.inl 58, -94750365214310400000), (Sum.inl 69, -814606572139315200000), (Sum.inl 70, -502053651283968000000), (Sum.inl 71, -937658762566041600000), (Sum.inl 256, 937658762566041600000), (Sum.inl 257, -379001460857241600000), (Sum.inl 495, -758002921714483200000)]

def originalMerge14 : Integer.Sparse OriginalKey := originalTerm14 ++ originalMerge13

theorem reducedMerge14Check : reducedMerge14 = Integer.Sparse.mergeBy masterLess reducedTerm14 reducedMerge13 := by decide +kernel

def reducedMerge15 : Integer.Sparse Master := [(Sum.inl 0, -94079494663741440000), (Sum.inl 1, -2838968629862400000), (Sum.inl 2, -102715286729932800000), (Sum.inl 9, -555781732827955200000), (Sum.inl 69, 741042310437273600000), (Sum.inl 70, 115936468726579200000), (Sum.inl 71, 1366148152147968000000)]

def originalMerge15 : Integer.Sparse OriginalKey := originalTerm17 ++ originalTerm18

theorem reducedMerge15Check : reducedMerge15 = Integer.Sparse.mergeBy masterLess reducedTerm17 reducedTerm18 := by decide +kernel

def reducedMerge16 : Integer.Sparse Master := [(Sum.inl 0, -14935163567063040000), (Sum.inl 1, 37337908917657600000), (Sum.inl 2, 37337908917657600000), (Sum.inl 9, -432949275589017600000), (Sum.inl 58, 119424485917900800000), (Sum.inl 69, 258800405004288000000), (Sum.inl 70, 258800405004288000000), (Sum.inl 257, 258800405004288000000)]

def originalMerge16 : Integer.Sparse OriginalKey := originalTerm19 ++ originalTerm20

theorem reducedMerge16Check : reducedMerge16 = Integer.Sparse.mergeBy masterLess reducedTerm19 reducedTerm20 := by decide +kernel

def reducedMerge17 : Integer.Sparse Master := [(Sum.inl 0, -109014658230804480000), (Sum.inl 1, 34498940287795200000), (Sum.inl 2, -65377377812275200000), (Sum.inl 9, -988731008416972800000), (Sum.inl 58, 119424485917900800000), (Sum.inl 69, 999842715441561600000), (Sum.inl 70, 374736873730867200000), (Sum.inl 71, 1366148152147968000000), (Sum.inl 257, 258800405004288000000)]

def originalMerge17 : Integer.Sparse OriginalKey := originalMerge15 ++ originalMerge16

theorem reducedMerge17Check : reducedMerge17 = Integer.Sparse.mergeBy masterLess reducedMerge15 reducedMerge16 := by decide +kernel

def reducedMerge18 : Integer.Sparse Master := [(Sum.inl 0, -187152888444641280000), (Sum.inl 1, -35948528024371200000), (Sum.inl 2, -237650667641856000000), (Sum.inl 5, 423915421070131200000), (Sum.inl 6, -165813139125043200000), (Sum.inl 7, -312552920855347200000), (Sum.inl 8, -312552920855347200000), (Sum.inl 9, -297176626704384000000), (Sum.inl 35, -379001460857241600000), (Sum.inl 58, 24674120703590400000), (Sum.inl 69, 185236143302246400000), (Sum.inl 70, -127316777553100800000), (Sum.inl 71, 428489389581926400000), (Sum.inl 256, 937658762566041600000), (Sum.inl 257, -120201055852953600000), (Sum.inl 495, -758002921714483200000)]

def originalMerge18 : Integer.Sparse OriginalKey := originalMerge14 ++ originalMerge17

theorem reducedMerge18Check : reducedMerge18 = Integer.Sparse.mergeBy masterLess reducedMerge14 reducedMerge17 := by decide +kernel

def reducedMerge19 : Integer.Sparse Master := [(Sum.inl 0, -71436456401264640000), (Sum.inl 1, -28619526594355200000), (Sum.inl 2, -66743899355750400000), (Sum.inl 3, 518743440978739200000), (Sum.inl 5, 345828960652492800000), (Sum.inl 6, -186872419386777600000), (Sum.inl 7, 823738423069900800000), (Sum.inl 8, 609989964182323200000), (Sum.inl 9, 1228003757671219200000), (Sum.inl 35, 864572401631232000000), (Sum.inl 52, 1037486881957478400000), (Sum.inl 58, -68644868589158400000), (Sum.inl 69, 1647476846139801600000), (Sum.inl 70, 722073429039513600000), (Sum.inl 71, 1738723369343385600000), (Sum.inl 256, -1556230322936217600000), (Sum.inl 257, 345828960652492800000), (Sum.inl 495, 518743440978739200000)]

def originalMerge19 : Integer.Sparse OriginalKey := originalTerm21 ++ originalTerm22

theorem reducedMerge19Check : reducedMerge19 = Integer.Sparse.mergeBy masterLess reducedTerm21 reducedTerm22 := by decide +kernel

def reducedMerge20 : Integer.Sparse Master := [(Sum.inl 0, 77974770343034880000), (Sum.inl 1, 64563594155827200000), (Sum.inl 2, -27436891500748800000), (Sum.inl 5, 43228620081561600000), (Sum.inl 6, -48492529608499200000), (Sum.inl 8, 257137032757248000000), (Sum.inl 9, 344711616786432000000), (Sum.inl 52, 345828960652492800000), (Sum.inl 58, -18842687294054400000), (Sum.inl 69, 474397477031116800000), (Sum.inl 71, 687188545840742400000), (Sum.inl 256, -518743440978739200000), (Sum.inl 495, 172914480326246400000)]

def originalMerge20 : Integer.Sparse OriginalKey := originalTerm23 ++ originalTerm24

theorem reducedMerge20Check : reducedMerge20 = Integer.Sparse.mergeBy masterLess reducedTerm23 reducedTerm24 := by decide +kernel

def reducedMerge21 : Integer.Sparse Master := [(Sum.inl 0, 6538313941770240000), (Sum.inl 1, 35944067561472000000), (Sum.inl 2, -94180790856499200000), (Sum.inl 3, 518743440978739200000), (Sum.inl 5, 389057580734054400000), (Sum.inl 6, -235364948995276800000), (Sum.inl 7, 823738423069900800000), (Sum.inl 8, 867126996939571200000), (Sum.inl 9, 1572715374457651200000), (Sum.inl 35, 864572401631232000000), (Sum.inl 52, 1383315842609971200000), (Sum.inl 58, -87487555883212800000), (Sum.inl 69, 2121874323170918400000), (Sum.inl 70, 722073429039513600000), (Sum.inl 71, 2425911915184128000000), (Sum.inl 256, -2074973763914956800000), (Sum.inl 257, 345828960652492800000), (Sum.inl 495, 691657921304985600000)]

def originalMerge21 : Integer.Sparse OriginalKey := originalMerge19 ++ originalMerge20

theorem reducedMerge21Check : reducedMerge21 = Integer.Sparse.mergeBy masterLess reducedMerge19 reducedMerge20 := by decide +kernel

def reducedMerge22 : Integer.Sparse Master := [(Sum.inl 0, 12988788535296000000), (Sum.inl 1, -27894614630400000000), (Sum.inl 2, -13589885030400000000), (Sum.inl 3, -52637642588160000000), (Sum.inl 5, -2859378278400000000), (Sum.inl 6, 19024271400960000000), (Sum.inl 7, -52637642588160000000), (Sum.inl 9, -65797053235200000000), (Sum.inl 35, -105275285176320000000), (Sum.inl 52, -52637642588160000000), (Sum.inl 58, 12444566077440000000), (Sum.inl 69, -52637642588160000000), (Sum.inl 70, -52637642588160000000), (Sum.inl 71, -146475414650880000000), (Sum.inl 256, 157912927764480000000), (Sum.inl 257, -52637642588160000000), (Sum.inl 495, -52637642588160000000)]

def originalMerge22 : Integer.Sparse OriginalKey := originalTerm25 ++ originalTerm26

theorem reducedMerge22Check : reducedMerge22 = Integer.Sparse.mergeBy masterLess reducedTerm25 reducedTerm26 := by decide +kernel

def reducedMerge23 : Integer.Sparse Master := [(Sum.inl 0, -11753330190336000000), (Sum.inl 1, -1660360284979200000), (Sum.inl 2, -132228181964390400000), (Sum.inl 5, 37129528590336000000), (Sum.inl 9, 51144629089075200000), (Sum.inl 35, 148518114361344000000), (Sum.inl 69, -46228856183193600000), (Sum.inl 70, 148518114361344000000), (Sum.inl 71, -46228856183193600000), (Sum.inl 257, 148518114361344000000)]

def originalMerge23 : Integer.Sparse OriginalKey := originalTerm27 ++ originalTerm28

theorem reducedMerge23Check : reducedMerge23 = Integer.Sparse.mergeBy masterLess reducedTerm27 reducedTerm28 := by decide +kernel

def reducedMerge24 : Integer.Sparse Master := [(Sum.inl 0, 1235458344960000000), (Sum.inl 1, -29554974915379200000), (Sum.inl 2, -145818066994790400000), (Sum.inl 3, -52637642588160000000), (Sum.inl 5, 34270150311936000000), (Sum.inl 6, 19024271400960000000), (Sum.inl 7, -52637642588160000000), (Sum.inl 9, -14652424146124800000), (Sum.inl 35, 43242829185024000000), (Sum.inl 52, -52637642588160000000), (Sum.inl 58, 12444566077440000000), (Sum.inl 69, -98866498771353600000), (Sum.inl 70, 95880471773184000000), (Sum.inl 71, -192704270834073600000), (Sum.inl 256, 157912927764480000000), (Sum.inl 257, 95880471773184000000), (Sum.inl 495, -52637642588160000000)]

def originalMerge24 : Integer.Sparse OriginalKey := originalMerge22 ++ originalMerge23

theorem reducedMerge24Check : reducedMerge24 = Integer.Sparse.mergeBy masterLess reducedMerge22 reducedMerge23 := by decide +kernel

def reducedMerge25 : Integer.Sparse Master := [(Sum.inl 0, 7773772286730240000), (Sum.inl 1, 6389092646092800000), (Sum.inl 2, -239998857851289600000), (Sum.inl 3, 466105798390579200000), (Sum.inl 5, 423327731045990400000), (Sum.inl 6, -216340677594316800000), (Sum.inl 7, 771100780481740800000), (Sum.inl 8, 867126996939571200000), (Sum.inl 9, 1558062950311526400000), (Sum.inl 35, 907815230816256000000), (Sum.inl 52, 1330678200021811200000), (Sum.inl 58, -75042989805772800000), (Sum.inl 69, 2023007824399564800000), (Sum.inl 70, 817953900812697600000), (Sum.inl 71, 2233207644350054400000), (Sum.inl 256, -1917060836150476800000), (Sum.inl 257, 441709432425676800000), (Sum.inl 495, 639020278716825600000)]

def originalMerge25 : Integer.Sparse OriginalKey := originalMerge21 ++ originalMerge24

theorem reducedMerge25Check : reducedMerge25 = Integer.Sparse.mergeBy masterLess reducedMerge21 reducedMerge24 := by decide +kernel

def reducedMerge26 : Integer.Sparse Master := [(Sum.inl 0, -179379116157911040000), (Sum.inl 1, -29559435378278400000), (Sum.inl 2, -477649525493145600000), (Sum.inl 3, 466105798390579200000), (Sum.inl 5, 847243152116121600000), (Sum.inl 6, -382153816719360000000), (Sum.inl 7, 458547859626393600000), (Sum.inl 8, 554574076084224000000), (Sum.inl 9, 1260886323607142400000), (Sum.inl 35, 528813769959014400000), (Sum.inl 52, 1330678200021811200000), (Sum.inl 58, -50368869102182400000), (Sum.inl 69, 2208243967701811200000), (Sum.inl 70, 690637123259596800000), (Sum.inl 71, 2661697033931980800000), (Sum.inl 256, -979402073584435200000), (Sum.inl 257, 321508376572723200000), (Sum.inl 495, -118982642997657600000)]

def originalMerge26 : Integer.Sparse OriginalKey := originalMerge18 ++ originalMerge25

theorem reducedMerge26Check : reducedMerge26 = Integer.Sparse.mergeBy masterLess reducedMerge18 reducedMerge25 := by decide +kernel

def reducedMerge27 : Integer.Sparse Master := [(Sum.inl 0, 21340843871836446720000), (Sum.inl 1, 1398283333873090560000), (Sum.inl 2, 1326189198938849280000), (Sum.inl 3, -159000043320115200000), (Sum.inl 5, 1352515460050944000000), (Sum.inl 6, -285506429593190400000), (Sum.inl 7, -1612666306776268800000), (Sum.inl 8, -70531765626470400000), (Sum.inl 9, 1414346350775500800000), (Sum.inl 35, -819346234097664000000), (Sum.inl 52, 1018125279166464000000), (Sum.inl 58, 11367816813158400000), (Sum.inl 69, 79459363307520000000), (Sum.inl 70, -1165972442923008000000), (Sum.inl 71, 1515426443093606400000), (Sum.inl 256, 895915451547648000000), (Sum.inl 257, -441923668416921600000), (Sum.inl 495, -431535563853004800000)]

def originalMerge27 : Integer.Sparse OriginalKey := originalMerge12 ++ originalMerge26

theorem reducedMerge27Check : reducedMerge27 = Integer.Sparse.mergeBy masterLess reducedMerge12 reducedMerge26 := by decide +kernel

def reducedMerge28 : Integer.Sparse Master := [(Sum.inl 0, -81129440044154880000), (Sum.inl 1, -268924527083520000000), (Sum.inl 2, 82915628440780800000), (Sum.inl 5, 132973773211238400000), (Sum.inl 7, 478088048148480000000), (Sum.inl 8, 53807044696473600000), (Sum.inl 9, 265947546422476800000), (Sum.inl 69, 478088048148480000000), (Sum.inl 70, 478088048148480000000), (Sum.inl 71, 107614089392947200000)]

def originalMerge28 : Integer.Sparse OriginalKey := originalTerm30 ++ originalTerm31

theorem reducedMerge28Check : reducedMerge28 = Integer.Sparse.mergeBy masterLess reducedTerm30 reducedTerm31 := by decide +kernel

def reducedMerge29 : Integer.Sparse Master := [(Sum.inl 0, -115618086988185600000), (Sum.inl 1, -182702909723443200000), (Sum.inl 2, 154766976240844800000), (Sum.inl 5, 132973773211238400000), (Sum.inl 6, -28740539120025600000), (Sum.inl 7, 478088048148480000000), (Sum.inl 8, 53807044696473600000), (Sum.inl 9, 323428624662528000000), (Sum.inl 35, 229924312960204800000), (Sum.inl 58, -14370269560012800000), (Sum.inl 69, 478088048148480000000), (Sum.inl 70, 478088048148480000000), (Sum.inl 71, 107614089392947200000), (Sum.inl 257, 229924312960204800000), (Sum.inl 495, 229924312960204800000)]

def originalMerge29 : Integer.Sparse OriginalKey := originalTerm29 ++ originalMerge28

theorem reducedMerge29Check : reducedMerge29 = Integer.Sparse.mergeBy masterLess reducedTerm29 reducedMerge28 := by decide +kernel

def reducedMerge30 : Integer.Sparse Master := [(Sum.inl 0, 70540340417003520000), (Sum.inl 1, 177345181027123200000), (Sum.inl 2, -83240646528614400000), (Sum.inl 5, -306643764820377600000), (Sum.inl 6, -70081235881574400000), (Sum.inl 9, -332962586114457600000), (Sum.inl 58, -70081235881574400000), (Sum.inl 256, 315825855528960000000)]

def originalMerge30 : Integer.Sparse OriginalKey := originalTerm32 ++ originalTerm33

theorem reducedMerge30Check : reducedMerge30 = Integer.Sparse.mergeBy masterLess reducedTerm32 reducedTerm33 := by decide +kernel

def reducedMerge31 : Integer.Sparse Master := [(Sum.inl 0, 94111544991744000000), (Sum.inl 1, 211892872878489600000), (Sum.inl 2, 211892872878489600000), (Sum.inl 6, -43110808680038400000), (Sum.inl 9, 298114490238566400000), (Sum.inl 58, -43110808680038400000), (Sum.inl 70, 1192457960954265600000), (Sum.inl 495, 689772938880614400000)]

def originalMerge31 : Integer.Sparse OriginalKey := originalTerm34 ++ originalTerm35

theorem reducedMerge31Check : reducedMerge31 = Integer.Sparse.mergeBy masterLess reducedTerm34 reducedTerm35 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
