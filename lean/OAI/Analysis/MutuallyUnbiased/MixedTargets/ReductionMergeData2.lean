import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData2
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData3
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData1

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge64 : Integer.Sparse Master := [(Sum.inl 0, -72938572881592320000), (Sum.inl 1, 165590224669900800000), (Sum.inl 2, 181360506868531200000), (Sum.inl 3, -89366440181760000000), (Sum.inl 5, 44683220090880000000), (Sum.inl 6, 49282697266790400000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, 54319358332108800000), (Sum.inl 35, -89366440181760000000), (Sum.inl 52, -89366440181760000000), (Sum.inl 59, 268099320545280000000), (Sum.inl 60, 233052238695628800000), (Sum.inl 128, 233052238695628800000)]

def originalMerge64 : Integer.Sparse OriginalKey := originalTerm66 ++ originalTerm67

theorem reducedMerge64Check : reducedMerge64 = Integer.Sparse.mergeBy masterLess reducedTerm66 reducedTerm67 := by decide +kernel

def reducedMerge65 : Integer.Sparse Master := [(Sum.inl 0, 48757171965788160000), (Sum.inl 1, -116307527403110400000), (Sum.inl 2, -82795112334950400000), (Sum.inl 5, 134049660272640000000), (Sum.inl 6, 120907004579020800000), (Sum.inl 59, 536198641090560000000), (Sum.inl 128, 483628018316083200000)]

def originalMerge65 : Integer.Sparse OriginalKey := originalTerm68 ++ originalTerm69

theorem reducedMerge65Check : reducedMerge65 = Integer.Sparse.mergeBy masterLess reducedTerm68 reducedTerm69 := by decide +kernel

def reducedMerge66 : Integer.Sparse Master := [(Sum.inl 0, -24181400915804160000), (Sum.inl 1, 49282697266790400000), (Sum.inl 2, 98565394533580800000), (Sum.inl 3, -89366440181760000000), (Sum.inl 5, 178732880363520000000), (Sum.inl 6, 170189701845811200000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, 54319358332108800000), (Sum.inl 35, -89366440181760000000), (Sum.inl 52, -89366440181760000000), (Sum.inl 59, 804297961635840000000), (Sum.inl 60, 233052238695628800000), (Sum.inl 128, 716680257011712000000)]

def originalMerge66 : Integer.Sparse OriginalKey := originalMerge64 ++ originalMerge65

theorem reducedMerge66Check : reducedMerge66 = Integer.Sparse.mergeBy masterLess reducedMerge64 reducedMerge65 := by decide +kernel

def reducedMerge67 : Integer.Sparse Master := [(Sum.inl 0, -41968844480102400000), (Sum.inl 1, 87486852534681600000), (Sum.inl 2, 101683506832588800000), (Sum.inl 3, -56786617191628800000), (Sum.inl 5, -14196654297907200000), (Sum.inl 6, 56165498778009600000), (Sum.inl 35, -56786617191628800000), (Sum.inl 52, -898647980448153600000)]

def originalMerge67 : Integer.Sparse OriginalKey := originalTerm70 ++ originalTerm71

theorem reducedMerge67Check : reducedMerge67 = Integer.Sparse.mergeBy masterLess reducedTerm70 reducedTerm71 := by decide +kernel

def reducedMerge68 : Integer.Sparse Master := [(Sum.inl 0, -146680351183134720000), (Sum.inl 1, 273813825658060800000), (Sum.inl 2, 309904152090624000000), (Sum.inl 3, 2141195359577702400000), (Sum.inl 5, -1095255302632243200000), (Sum.inl 6, 100368532480204800000), (Sum.inl 7, 3211793039366553600000), (Sum.inl 8, 1070597679788851200000), (Sum.inl 9, -267649419947212800000), (Sum.inl 26, 535298839894425600000), (Sum.inl 35, 4183760227781836800000), (Sum.inl 52, 535298839894425600000), (Sum.inl 67, 1070597679788851200000), (Sum.inl 69, 2141195359577702400000), (Sum.inl 70, 2141195359577702400000), (Sum.inl 71, 535298839894425600000), (Sum.inl 257, 535298839894425600000)]

def originalMerge68 : Integer.Sparse OriginalKey := originalTerm72 ++ originalTerm73

theorem reducedMerge68Check : reducedMerge68 = Integer.Sparse.mergeBy masterLess reducedTerm72 reducedTerm73 := by decide +kernel

def reducedMerge69 : Integer.Sparse Master := [(Sum.inl 0, -188649195663237120000), (Sum.inl 1, 361300678192742400000), (Sum.inl 2, 411587658923212800000), (Sum.inl 3, 2084408742386073600000), (Sum.inl 5, -1109451956930150400000), (Sum.inl 6, 156534031258214400000), (Sum.inl 7, 3211793039366553600000), (Sum.inl 8, 1070597679788851200000), (Sum.inl 9, -267649419947212800000), (Sum.inl 26, 535298839894425600000), (Sum.inl 35, 4126973610590208000000), (Sum.inl 52, -363349140553728000000), (Sum.inl 67, 1070597679788851200000), (Sum.inl 69, 2141195359577702400000), (Sum.inl 70, 2141195359577702400000), (Sum.inl 71, 535298839894425600000), (Sum.inl 257, 535298839894425600000)]

def originalMerge69 : Integer.Sparse OriginalKey := originalMerge67 ++ originalMerge68

theorem reducedMerge69Check : reducedMerge69 = Integer.Sparse.mergeBy masterLess reducedMerge67 reducedMerge68 := by decide +kernel

def reducedMerge70 : Integer.Sparse Master := [(Sum.inl 0, -212830596579041280000), (Sum.inl 1, 410583375459532800000), (Sum.inl 2, 510153053456793600000), (Sum.inl 3, 1995042302204313600000), (Sum.inl 5, -930719076566630400000), (Sum.inl 6, 326723733104025600000), (Sum.inl 7, 3211793039366553600000), (Sum.inl 8, 1070597679788851200000), (Sum.inl 9, -267649419947212800000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, 54319358332108800000), (Sum.inl 26, 535298839894425600000), (Sum.inl 35, 4037607170408448000000), (Sum.inl 52, -452715580735488000000), (Sum.inl 59, 804297961635840000000), (Sum.inl 60, 233052238695628800000), (Sum.inl 67, 1070597679788851200000), (Sum.inl 69, 2141195359577702400000), (Sum.inl 70, 2141195359577702400000), (Sum.inl 71, 535298839894425600000), (Sum.inl 128, 716680257011712000000), (Sum.inl 257, 535298839894425600000)]

def originalMerge70 : Integer.Sparse OriginalKey := originalMerge66 ++ originalMerge69

theorem reducedMerge70Check : reducedMerge70 = Integer.Sparse.mergeBy masterLess reducedMerge66 reducedMerge69 := by decide +kernel

def reducedMerge71 : Integer.Sparse Master := [(Sum.inl 0, -97903485876510720000), (Sum.inl 1, -353383220684390400000), (Sum.inl 2, -138135047152435200000), (Sum.inl 3, 2205903090017894400000), (Sum.inl 5, 1365178237658726400000), (Sum.inl 6, 117044171596800000000), (Sum.inl 7, 2754767037844684800000), (Sum.inl 8, -209413808632627200000), (Sum.inl 9, -267649419947212800000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, 54319358332108800000), (Sum.inl 26, 535298839894425600000), (Sum.inl 35, 3768728761250611200000), (Sum.inl 52, -1016960876789760000000), (Sum.inl 59, 804297961635840000000), (Sum.inl 60, 315769437152870400000), (Sum.inl 67, 1070597679788851200000), (Sum.inl 69, 2141195359577702400000), (Sum.inl 70, 2141195359577702400000), (Sum.inl 71, 535298839894425600000), (Sum.inl 128, 716680257011712000000), (Sum.inl 257, 535298839894425600000)]

def originalMerge71 : Integer.Sparse OriginalKey := originalMerge63 ++ originalMerge70

theorem reducedMerge71Check : reducedMerge71 = Integer.Sparse.mergeBy masterLess reducedMerge63 reducedMerge70 := by decide +kernel

def reducedMerge72 : Integer.Sparse Master := [(Sum.inl 0, 158253422864302080000), (Sum.inl 1, -236437845519052800000), (Sum.inl 2, 202689392745369600000), (Sum.inl 5, -680921208782438400000), (Sum.inl 6, 87954383875276800000), (Sum.inl 7, 1230716693141913600000), (Sum.inl 8, 438804897708441600000), (Sum.inl 9, -307679173285478400000), (Sum.inl 35, 968465244295987200000), (Sum.inl 52, 438804897708441600000), (Sum.inl 67, 176553448862515200000), (Sum.inl 69, 1054163244279398400000), (Sum.inl 70, 791911795433472000000), (Sum.inl 71, 438804897708441600000), (Sum.inl 257, 176553448862515200000)]

def originalMerge72 : Integer.Sparse OriginalKey := originalTerm75 ++ originalTerm76

theorem reducedMerge72Check : reducedMerge72 = Integer.Sparse.mergeBy masterLess reducedTerm75 reducedTerm76 := by decide +kernel

def reducedMerge73 : Integer.Sparse Master := [(Sum.inl 0, 58581807404359680000), (Sum.inl 1, -136766230059110400000), (Sum.inl 2, -146161261364428800000), (Sum.inl 5, -680921208782438400000), (Sum.inl 6, 87954383875276800000), (Sum.inl 7, 1230716693141913600000), (Sum.inl 8, 438804897708441600000), (Sum.inl 9, 91007288554291200000), (Sum.inl 35, 968465244295987200000), (Sum.inl 52, 438804897708441600000), (Sum.inl 58, -49835807729971200000), (Sum.inl 67, 176553448862515200000), (Sum.inl 69, 1054163244279398400000), (Sum.inl 70, 791911795433472000000), (Sum.inl 71, 438804897708441600000), (Sum.inl 257, 176553448862515200000)]

def originalMerge73 : Integer.Sparse OriginalKey := originalTerm74 ++ originalMerge72

theorem reducedMerge73Check : reducedMerge73 = Integer.Sparse.mergeBy masterLess reducedTerm74 reducedMerge72 := by decide +kernel

def reducedMerge74 : Integer.Sparse Master := [(Sum.inl 0, 37084305683496960000), (Sum.inl 1, -96101158087065600000), (Sum.inl 2, -70668890372505600000), (Sum.inl 3, -207147341669990400000), (Sum.inl 5, 259549043746406400000), (Sum.inl 6, -26431426035302400000), (Sum.inl 7, -415524416657817600000), (Sum.inl 8, -414294683339980800000), (Sum.inl 9, -103573670834995200000), (Sum.inl 35, -209606808305664000000), (Sum.inl 58, 6550212759552000000), (Sum.inl 69, -207147341669990400000), (Sum.inl 70, -104803404152832000000), (Sum.inl 71, -207147341669990400000)]

def originalMerge74 : Integer.Sparse OriginalKey := originalTerm77 ++ originalTerm78

theorem reducedMerge74Check : reducedMerge74 = Integer.Sparse.mergeBy masterLess reducedTerm77 reducedTerm78 := by decide +kernel

def reducedMerge75 : Integer.Sparse Master := [(Sum.inl 0, -100455816465285120000), (Sum.inl 1, 123951431974809600000), (Sum.inl 2, -341502246844416000000), (Sum.inl 3, -541647721488384000000), (Sum.inl 5, 270823860744192000000), (Sum.inl 6, -103045158236160000000), (Sum.inl 7, -541647721488384000000), (Sum.inl 8, 103573670834995200000), (Sum.inl 9, -135411930372096000000), (Sum.inl 35, -1083295442976768000000), (Sum.inl 52, -1083295442976768000000), (Sum.inl 58, 27379628165836800000), (Sum.inl 69, -541647721488384000000), (Sum.inl 71, 103573670834995200000), (Sum.inl 495, -541647721488384000000)]

def originalMerge75 : Integer.Sparse OriginalKey := originalTerm79 ++ originalTerm80

theorem reducedMerge75Check : reducedMerge75 = Integer.Sparse.mergeBy masterLess reducedTerm79 reducedTerm80 := by decide +kernel

def reducedMerge76 : Integer.Sparse Master := [(Sum.inl 0, -63371510781788160000), (Sum.inl 1, 27850273887744000000), (Sum.inl 2, -412171137216921600000), (Sum.inl 3, -748795063158374400000), (Sum.inl 5, 530372904490598400000), (Sum.inl 6, -129476584271462400000), (Sum.inl 7, -957172138146201600000), (Sum.inl 8, -310721012504985600000), (Sum.inl 9, -238985601207091200000), (Sum.inl 35, -1292902251282432000000), (Sum.inl 52, -1083295442976768000000), (Sum.inl 58, 33929840925388800000), (Sum.inl 69, -748795063158374400000), (Sum.inl 70, -104803404152832000000), (Sum.inl 71, -103573670834995200000), (Sum.inl 495, -541647721488384000000)]

def originalMerge76 : Integer.Sparse OriginalKey := originalMerge74 ++ originalMerge75

theorem reducedMerge76Check : reducedMerge76 = Integer.Sparse.mergeBy masterLess reducedMerge74 reducedMerge75 := by decide +kernel

def reducedMerge77 : Integer.Sparse Master := [(Sum.inl 0, -4789703377428480000), (Sum.inl 1, -108915956171366400000), (Sum.inl 2, -558332398581350400000), (Sum.inl 3, -748795063158374400000), (Sum.inl 5, -150548304291840000000), (Sum.inl 6, -41522200396185600000), (Sum.inl 7, 273544554995712000000), (Sum.inl 8, 128083885203456000000), (Sum.inl 9, -147978312652800000000), (Sum.inl 35, -324437006986444800000), (Sum.inl 52, -644490545268326400000), (Sum.inl 58, -15905966804582400000), (Sum.inl 67, 176553448862515200000), (Sum.inl 69, 305368181121024000000), (Sum.inl 70, 687108391280640000000), (Sum.inl 71, 335231226873446400000), (Sum.inl 257, 176553448862515200000), (Sum.inl 495, -541647721488384000000)]

def originalMerge77 : Integer.Sparse OriginalKey := originalMerge73 ++ originalMerge76

theorem reducedMerge77Check : reducedMerge77 = Integer.Sparse.mergeBy masterLess reducedMerge73 reducedMerge76 := by decide +kernel

def reducedMerge78 : Integer.Sparse Master := [(Sum.inl 0, 59909030263111680000), (Sum.inl 1, -94845013143552000000), (Sum.inl 2, 56448683827200000000), (Sum.inl 3, -17154413582745600000), (Sum.inl 5, -191485908143308800000), (Sum.inl 6, -21791436820070400000), (Sum.inl 7, 348662989121126400000), (Sum.inl 8, 382971816286617600000), (Sum.inl 9, 87165747280281600000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, -68617654330982400000), (Sum.inl 67, -34308827165491200000), (Sum.inl 69, 191485908143308800000), (Sum.inl 70, -17154413582745600000), (Sum.inl 71, 191485908143308800000), (Sum.inl 257, -17154413582745600000)]

def originalMerge78 : Integer.Sparse OriginalKey := originalTerm81 ++ originalTerm82

theorem reducedMerge78Check : reducedMerge78 = Integer.Sparse.mergeBy masterLess reducedTerm81 reducedTerm82 := by decide +kernel

def reducedMerge79 : Integer.Sparse Master := [(Sum.inl 1, -9506416943923200000), (Sum.inl 2, -7922014119936000000), (Sum.inl 3, 76051335551385600000), (Sum.inl 5, 38025667775692800000), (Sum.inl 6, 4753208471961600000), (Sum.inl 7, 25350445183795200000), (Sum.inl 9, 25350445183795200000), (Sum.inl 35, 50700890367590400000), (Sum.inl 58, -3168805647974400000), (Sum.inl 69, 101401780735180800000), (Sum.inl 70, 50700890367590400000)]

def originalMerge79 : Integer.Sparse OriginalKey := originalTerm83 ++ originalTerm84

theorem reducedMerge79Check : reducedMerge79 = Integer.Sparse.mergeBy masterLess reducedTerm83 reducedTerm84 := by decide +kernel

def reducedMerge80 : Integer.Sparse Master := [(Sum.inl 0, 59909030263111680000), (Sum.inl 1, -104351430087475200000), (Sum.inl 2, 48526669707264000000), (Sum.inl 3, 58896921968640000000), (Sum.inl 5, -153460240367616000000), (Sum.inl 6, -17038228348108800000), (Sum.inl 7, 374013434304921600000), (Sum.inl 8, 382971816286617600000), (Sum.inl 9, 112516192464076800000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, -17916763963392000000), (Sum.inl 58, -3168805647974400000), (Sum.inl 67, -34308827165491200000), (Sum.inl 69, 292887688878489600000), (Sum.inl 70, 33546476784844800000), (Sum.inl 71, 191485908143308800000), (Sum.inl 257, -17154413582745600000)]

def originalMerge80 : Integer.Sparse OriginalKey := originalMerge78 ++ originalMerge79

theorem reducedMerge80Check : reducedMerge80 = Integer.Sparse.mergeBy masterLess reducedMerge78 reducedMerge79 := by decide +kernel

def reducedMerge81 : Integer.Sparse Master := [(Sum.inl 0, -140133420229017600000), (Sum.inl 1, -522315475399065600000), (Sum.inl 2, -12739401839001600000), (Sum.inl 3, -407660858848051200000), (Sum.inl 5, 203830429424025600000), (Sum.inl 6, 76436411034009600000), (Sum.inl 9, -254788036780032000000), (Sum.inl 35, -407660858848051200000), (Sum.inl 58, -12739401839001600000), (Sum.inl 69, -407660858848051200000), (Sum.inl 70, -407660858848051200000)]

def originalMerge81 : Integer.Sparse OriginalKey := originalTerm85 ++ originalTerm86

theorem reducedMerge81Check : reducedMerge81 = Integer.Sparse.mergeBy masterLess reducedTerm85 reducedTerm86 := by decide +kernel

def reducedMerge82 : Integer.Sparse Master := [(Sum.inl 0, 113689278739169280000), (Sum.inl 1, -386136786960691200000), (Sum.inl 2, 51955192287129600000), (Sum.inl 3, 541647721488384000000), (Sum.inl 5, -99207510983884800000), (Sum.inl 6, -76757070033100800000), (Sum.inl 7, 1228113120529612800000), (Sum.inl 8, 541647721488384000000), (Sum.inl 9, 307028280132403200000), (Sum.inl 35, 686465399041228800000), (Sum.inl 70, 144817677552844800000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000)]

def originalMerge82 : Integer.Sparse OriginalKey := originalTerm87 ++ originalTerm88

theorem reducedMerge82Check : reducedMerge82 = Integer.Sparse.mergeBy masterLess reducedTerm87 reducedTerm88 := by decide +kernel

def reducedMerge83 : Integer.Sparse Master := [(Sum.inl 0, -26444141489848320000), (Sum.inl 1, -908452262359756800000), (Sum.inl 2, 39215790448128000000), (Sum.inl 3, 133986862640332800000), (Sum.inl 5, 104622918440140800000), (Sum.inl 6, -320658999091200000), (Sum.inl 7, 1228113120529612800000), (Sum.inl 8, 541647721488384000000), (Sum.inl 9, 52240243352371200000), (Sum.inl 35, 278804540193177600000), (Sum.inl 58, -12739401839001600000), (Sum.inl 69, -407660858848051200000), (Sum.inl 70, -262843181295206400000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000)]

def originalMerge83 : Integer.Sparse OriginalKey := originalMerge81 ++ originalMerge82

theorem reducedMerge83Check : reducedMerge83 = Integer.Sparse.mergeBy masterLess reducedMerge81 reducedMerge82 := by decide +kernel

def reducedMerge84 : Integer.Sparse Master := [(Sum.inl 0, 33464888773263360000), (Sum.inl 1, -1012803692447232000000), (Sum.inl 2, 87742460155392000000), (Sum.inl 3, 192883784608972800000), (Sum.inl 5, -48837321927475200000), (Sum.inl 6, -17358887347200000000), (Sum.inl 7, 1602126554834534400000), (Sum.inl 8, 924619537775001600000), (Sum.inl 9, 164756435816448000000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, 260887776229785600000), (Sum.inl 58, -15908207486976000000), (Sum.inl 67, -34308827165491200000), (Sum.inl 69, -114773169969561600000), (Sum.inl 70, -229296704510361600000), (Sum.inl 71, 191485908143308800000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000), (Sum.inl 257, -17154413582745600000)]

def originalMerge84 : Integer.Sparse OriginalKey := originalMerge80 ++ originalMerge83

theorem reducedMerge84Check : reducedMerge84 = Integer.Sparse.mergeBy masterLess reducedMerge80 reducedMerge83 := by decide +kernel

def reducedMerge85 : Integer.Sparse Master := [(Sum.inl 0, 28675185395834880000), (Sum.inl 1, -1121719648618598400000), (Sum.inl 2, -470589938425958400000), (Sum.inl 3, -555911278549401600000), (Sum.inl 5, -199385626219315200000), (Sum.inl 6, -58881087743385600000), (Sum.inl 7, 1875671109830246400000), (Sum.inl 8, 1052703422978457600000), (Sum.inl 9, 16778123163648000000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, -63549230756659200000), (Sum.inl 52, -644490545268326400000), (Sum.inl 58, -31814174291558400000), (Sum.inl 67, 142244621697024000000), (Sum.inl 69, 190595011151462400000), (Sum.inl 70, 457811686770278400000), (Sum.inl 71, 526717135016755200000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000), (Sum.inl 257, 159399035279769600000), (Sum.inl 495, -541647721488384000000)]

def originalMerge85 : Integer.Sparse OriginalKey := originalMerge77 ++ originalMerge84

theorem reducedMerge85Check : reducedMerge85 = Integer.Sparse.mergeBy masterLess reducedMerge77 reducedMerge84 := by decide +kernel

def reducedMerge86 : Integer.Sparse Master := [(Sum.inl 0, -69228300480675840000), (Sum.inl 1, -1475102869302988800000), (Sum.inl 2, -608724985578393600000), (Sum.inl 3, 1649991811468492800000), (Sum.inl 5, 1165792611439411200000), (Sum.inl 6, 58163083853414400000), (Sum.inl 7, 4630438147674931200000), (Sum.inl 8, 843289614345830400000), (Sum.inl 9, -250871296783564800000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, 54319358332108800000), (Sum.inl 26, 518144426311680000000), (Sum.inl 35, 3705179530493952000000), (Sum.inl 52, -1661451422058086400000), (Sum.inl 58, -31814174291558400000), (Sum.inl 59, 804297961635840000000), (Sum.inl 60, 315769437152870400000), (Sum.inl 67, 1212842301485875200000), (Sum.inl 69, 2331790370729164800000), (Sum.inl 70, 2599007046347980800000), (Sum.inl 71, 1062015974911180800000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 128, 716680257011712000000), (Sum.inl 256, -1624943164465152000000), (Sum.inl 257, 694697875174195200000), (Sum.inl 495, -541647721488384000000)]

def originalMerge86 : Integer.Sparse OriginalKey := originalMerge71 ++ originalMerge85

theorem reducedMerge86Check : reducedMerge86 = Integer.Sparse.mergeBy masterLess reducedMerge71 reducedMerge85 := by decide +kernel

def reducedMerge87 : Integer.Sparse Master := [(Sum.inl 0, -22184324592353280000), (Sum.inl 1, -188384061693542400000), (Sum.inl 2, -47676947344588800000), (Sum.inl 5, -24688047631564800000), (Sum.inl 6, -10644875897241600000), (Sum.inl 7, 269070204882124800000), (Sum.inl 9, 42579503588966400000), (Sum.inl 35, -98752190526259200000), (Sum.inl 67, -98752190526259200000), (Sum.inl 69, 269070204882124800000), (Sum.inl 257, -98752190526259200000)]

def originalMerge87 : Integer.Sparse OriginalKey := originalTerm90 ++ originalTerm91

theorem reducedMerge87Check : reducedMerge87 = Integer.Sparse.mergeBy masterLess reducedTerm90 reducedTerm91 := by decide +kernel

def reducedMerge88 : Integer.Sparse Master := [(Sum.inl 0, -58435109384601600000), (Sum.inl 1, -110703808567296000000), (Sum.inl 2, -60623656198963200000), (Sum.inl 5, -24688047631564800000), (Sum.inl 6, -23591584751616000000), (Sum.inl 7, 269070204882124800000), (Sum.inl 8, 207147341669990400000), (Sum.inl 9, 94366339006464000000), (Sum.inl 35, -98752190526259200000), (Sum.inl 67, -98752190526259200000), (Sum.inl 69, 269070204882124800000), (Sum.inl 71, 207147341669990400000), (Sum.inl 257, -98752190526259200000)]

def originalMerge88 : Integer.Sparse OriginalKey := originalTerm89 ++ originalMerge87

theorem reducedMerge88Check : reducedMerge88 = Integer.Sparse.mergeBy masterLess reducedTerm89 reducedMerge87 := by decide +kernel

def reducedMerge89 : Integer.Sparse Master := [(Sum.inl 0, 289480239059558400000), (Sum.inl 1, -500624680124620800000), (Sum.inl 2, 235007393983488000000), (Sum.inl 5, 95451811673702400000), (Sum.inl 6, 664043215352832000000), (Sum.inl 8, 626686383955968000000), (Sum.inl 35, 1253372767911936000000), (Sum.inl 67, 626686383955968000000)]

def originalMerge89 : Integer.Sparse OriginalKey := originalTerm92 ++ originalTerm93

theorem reducedMerge89Check : reducedMerge89 = Integer.Sparse.mergeBy masterLess reducedTerm92 reducedTerm93 := by decide +kernel

def reducedMerge90 : Integer.Sparse Master := [(Sum.inl 0, -241954585850880000000), (Sum.inl 1, 386954463071232000000), (Sum.inl 2, -476621953145856000000), (Sum.inl 3, -789361054433280000000), (Sum.inl 5, 1019307678068736000000), (Sum.inl 6, -180611557733376000000), (Sum.inl 7, -1578722108866560000000), (Sum.inl 8, -789361054433280000000), (Sum.inl 35, -919786494541824000000)]

def originalMerge90 : Integer.Sparse OriginalKey := originalTerm94 ++ originalTerm95

theorem reducedMerge90Check : reducedMerge90 = Integer.Sparse.mergeBy masterLess reducedTerm94 reducedTerm95 := by decide +kernel

def reducedMerge91 : Integer.Sparse Master := [(Sum.inl 0, 47525653208678400000), (Sum.inl 1, -113670217053388800000), (Sum.inl 2, -241614559162368000000), (Sum.inl 3, -789361054433280000000), (Sum.inl 5, 1114759489742438400000), (Sum.inl 6, 483431657619456000000), (Sum.inl 7, -1578722108866560000000), (Sum.inl 8, -162674670477312000000), (Sum.inl 35, 333586273370112000000), (Sum.inl 67, 626686383955968000000)]

def originalMerge91 : Integer.Sparse OriginalKey := originalMerge89 ++ originalMerge90

theorem reducedMerge91Check : reducedMerge91 = Integer.Sparse.mergeBy masterLess reducedMerge89 reducedMerge90 := by decide +kernel

def reducedMerge92 : Integer.Sparse Master := [(Sum.inl 0, -10909456175923200000), (Sum.inl 1, -224374025620684800000), (Sum.inl 2, -302238215361331200000), (Sum.inl 3, -789361054433280000000), (Sum.inl 5, 1090071442110873600000), (Sum.inl 6, 459840072867840000000), (Sum.inl 7, -1309651903984435200000), (Sum.inl 8, 44472671192678400000), (Sum.inl 9, 94366339006464000000), (Sum.inl 35, 234834082843852800000), (Sum.inl 67, 527934193429708800000), (Sum.inl 69, 269070204882124800000), (Sum.inl 71, 207147341669990400000), (Sum.inl 257, -98752190526259200000)]

def originalMerge92 : Integer.Sparse OriginalKey := originalMerge88 ++ originalMerge91

theorem reducedMerge92Check : reducedMerge92 = Integer.Sparse.mergeBy masterLess reducedMerge88 reducedMerge91 := by decide +kernel

def reducedMerge93 : Integer.Sparse Master := [(Sum.inl 0, 66274055221248000000), (Sum.inl 1, -178540491025612800000), (Sum.inl 2, -156261526028697600000), (Sum.inl 3, -205685647559884800000), (Sum.inl 5, 261101640167424000000), (Sum.inl 6, -150832494721843200000), (Sum.inl 7, -205685647559884800000), (Sum.inl 26, -102842823779942400000), (Sum.inl 35, -1044406560669696000000), (Sum.inl 52, -838720913109811200000), (Sum.inl 67, -102842823779942400000)]

def originalMerge93 : Integer.Sparse OriginalKey := originalTerm96 ++ originalTerm97

theorem reducedMerge93Check : reducedMerge93 = Integer.Sparse.mergeBy masterLess reducedTerm96 reducedTerm97 := by decide +kernel

def reducedMerge94 : Integer.Sparse Master := [(Sum.inl 0, 52981975901675520000), (Sum.inl 1, -97945332710400000000), (Sum.inl 2, 109112309552332800000), (Sum.inl 5, 333929093595955200000), (Sum.inl 7, -115704474491289600000), (Sum.inl 8, -988602950909952000000), (Sum.inl 35, 872898476418662400000), (Sum.inl 67, 872898476418662400000)]

def originalMerge94 : Integer.Sparse OriginalKey := originalTerm98 ++ originalTerm99

theorem reducedMerge94Check : reducedMerge94 = Integer.Sparse.mergeBy masterLess reducedTerm98 reducedTerm99 := by decide +kernel

def reducedMerge95 : Integer.Sparse Master := [(Sum.inl 0, 119256031122923520000), (Sum.inl 1, -276485823736012800000), (Sum.inl 2, -47149216476364800000), (Sum.inl 3, -205685647559884800000), (Sum.inl 5, 595030733763379200000), (Sum.inl 6, -150832494721843200000), (Sum.inl 7, -321390122051174400000), (Sum.inl 8, -988602950909952000000), (Sum.inl 26, -102842823779942400000), (Sum.inl 35, -171508084251033600000), (Sum.inl 52, -838720913109811200000), (Sum.inl 67, 770055652638720000000)]

def originalMerge95 : Integer.Sparse OriginalKey := originalMerge93 ++ originalMerge94

theorem reducedMerge95Check : reducedMerge95 = Integer.Sparse.mergeBy masterLess reducedMerge93 reducedMerge94 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
