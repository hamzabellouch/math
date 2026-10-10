import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1232 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4071 x + ((3 : ℝ) * Sparse.eval nodeValue4121 x + ((1 : ℝ) * Sparse.eval nodeValue4134 x + ((1 : ℝ) * Sparse.eval nodeValue4137 x + ((6 : ℝ) * Sparse.eval nodeValue4212 x + ((3 : ℝ) * Sparse.eval nodeValue4225 x + ((3 : ℝ) * Sparse.eval nodeValue4228 x + ((3 : ℝ) * Sparse.eval nodeValue4272 x + ((3 : ℝ) * Sparse.eval nodeValue4273 x + ((1 : ℝ) * Sparse.eval nodeValue4280 x + ((3 : ℝ) * Sparse.eval nodeValue4431 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + 0))))))))))))

def numericRow1232 : Integer.Sparse Master := [(Sum.inr 555, -3), (Sum.inr 564, -1), (Sum.inr 671, -3), (Sum.inr 695, -1), (Sum.inr 715, -6), (Sum.inr 726, -3), (Sum.inr 753, -6), (Sum.inr 774, -3), (Sum.inr 815, -3), (Sum.inr 826, -3), (Sum.inr 832, -1), (Sum.inr 862, -1), (Sum.inr 1012, -3), (Sum.inr 1094, -1), (Sum.inr 1627, -3), (Sum.inr 1741, -1), (Sum.inr 4071, 4)]

theorem reindexCheck1232 : Integer.Sparse.reindex keyMap MixedData.row1232 = numericRow1232 := by decide +kernel

theorem numericCheck1232 (x : Master → ℝ) : Integer.Sparse.eval numericRow1232 x =
    (4 : ℝ) * reducedSource1232 x := by
  norm_num [numericRow1232, reducedSource1232, Integer.Sparse.eval, Sparse.eval, nodeValue4071, nodeValue4121, nodeValue4134, nodeValue4137, nodeValue4212, nodeValue4225, nodeValue4228, nodeValue4272, nodeValue4273, nodeValue4280, nodeValue4431, nodeValue4510, nodeValue4511]; ring

noncomputable def reducedSource1233 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4070 x + ((3 : ℝ) * Sparse.eval nodeValue4122 x + ((1 : ℝ) * Sparse.eval nodeValue4136 x + ((1 : ℝ) * Sparse.eval nodeValue4138 x + ((6 : ℝ) * Sparse.eval nodeValue4213 x + ((3 : ℝ) * Sparse.eval nodeValue4227 x + ((3 : ℝ) * Sparse.eval nodeValue4229 x + ((3 : ℝ) * Sparse.eval nodeValue4269 x + ((3 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4285 x + ((3 : ℝ) * Sparse.eval nodeValue4428 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + 0))))))))))))

def numericRow1233 : Integer.Sparse Master := [(Sum.inr 556, -3), (Sum.inr 566, -1), (Sum.inr 670, -3), (Sum.inr 694, -1), (Sum.inr 716, -6), (Sum.inr 729, -3), (Sum.inr 752, -6), (Sum.inr 773, -3), (Sum.inr 813, -3), (Sum.inr 853, -3), (Sum.inr 860, -2), (Sum.inr 1009, -3), (Sum.inr 1091, -1), (Sum.inr 1630, -3), (Sum.inr 1756, -1), (Sum.inr 4070, 4)]

theorem reindexCheck1233 : Integer.Sparse.reindex keyMap MixedData.row1233 = numericRow1233 := by decide +kernel

theorem numericCheck1233 (x : Master → ℝ) : Integer.Sparse.eval numericRow1233 x =
    (4 : ℝ) * reducedSource1233 x := by
  norm_num [numericRow1233, reducedSource1233, Integer.Sparse.eval, Sparse.eval, nodeValue4070, nodeValue4122, nodeValue4136, nodeValue4138, nodeValue4213, nodeValue4227, nodeValue4229, nodeValue4269, nodeValue4270, nodeValue4285, nodeValue4428, nodeValue4505, nodeValue4507]; ring

noncomputable def reducedSource1234 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4058 x + ((1 : ℝ) * Sparse.eval nodeValue4060 x + ((1 : ℝ) * Sparse.eval nodeValue4061 x + ((6 : ℝ) * Sparse.eval nodeValue4064 x + ((3 : ℝ) * Sparse.eval nodeValue4066 x + ((3 : ℝ) * Sparse.eval nodeValue4067 x + ((3 : ℝ) * Sparse.eval nodeValue4069 x + ((3 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4071 x + ((1 : ℝ) * Sparse.eval nodeValue4072 x + ((3 : ℝ) * Sparse.eval nodeValue4081 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))))))))))

def numericRow1234 : Integer.Sparse Master := [(Sum.inr 4058, 3), (Sum.inr 4060, 1), (Sum.inr 4061, 1), (Sum.inr 4064, 6), (Sum.inr 4066, 3), (Sum.inr 4067, 3), (Sum.inr 4069, 3), (Sum.inr 4070, 3), (Sum.inr 4071, 1), (Sum.inr 4072, 1), (Sum.inr 4081, 3), (Sum.inr 4084, 1), (Sum.inr 4085, 1)]

theorem reindexCheck1234 : Integer.Sparse.reindex keyMap MixedData.row1234 = numericRow1234 := by decide +kernel

theorem numericCheck1234 (x : Master → ℝ) : Integer.Sparse.eval numericRow1234 x =
    (1 : ℝ) * reducedSource1234 x := by
  norm_num [numericRow1234, reducedSource1234, Integer.Sparse.eval, Sparse.eval, nodeValue4058, nodeValue4060, nodeValue4061, nodeValue4064, nodeValue4066, nodeValue4067, nodeValue4069, nodeValue4070, nodeValue4071, nodeValue4072, nodeValue4081, nodeValue4084, nodeValue4085]

noncomputable def reducedSource1235 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue616 x + ((2 : ℝ) * Sparse.eval nodeValue935 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1235 : Integer.Sparse Master := [(Sum.inr 616, 1), (Sum.inr 935, 2), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1235 : Integer.Sparse.reindex keyMap MixedData.row1235 = numericRow1235 := by decide +kernel

theorem numericCheck1235 (x : Master → ℝ) : Integer.Sparse.eval numericRow1235 x =
    (1 : ℝ) * reducedSource1235 x := by
  norm_num [numericRow1235, reducedSource1235, Integer.Sparse.eval, Sparse.eval, nodeValue616, nodeValue935, nodeValue1063, nodeValue1083, nodeValue1087, nodeValue4084]

noncomputable def reducedSource1236 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1318 x + ((1 : ℝ) * Sparse.eval nodeValue1324 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((1 : ℝ) * Sparse.eval nodeValue1375 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1236 : Integer.Sparse Master := [(Sum.inr 1318, 2), (Sum.inr 1324, 1), (Sum.inr 1325, 1), (Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1236 : Integer.Sparse.reindex keyMap MixedData.row1236 = numericRow1236 := by decide +kernel

theorem numericCheck1236 (x : Master → ℝ) : Integer.Sparse.eval numericRow1236 x =
    (1 : ℝ) * reducedSource1236 x := by
  norm_num [numericRow1236, reducedSource1236, Integer.Sparse.eval, Sparse.eval, nodeValue1318, nodeValue1324, nodeValue1325, nodeValue1375, nodeValue2889, nodeValue4092]

noncomputable def reducedSource1237 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1237 : Integer.Sparse Master := [(Sum.inr 1736, 2), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1751, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1237 : Integer.Sparse.reindex keyMap MixedData.row1237 = numericRow1237 := by decide +kernel

theorem numericCheck1237 (x : Master → ℝ) : Integer.Sparse.eval numericRow1237 x =
    (1 : ℝ) * reducedSource1237 x := by
  norm_num [numericRow1237, reducedSource1237, Integer.Sparse.eval, Sparse.eval, nodeValue1736, nodeValue1738, nodeValue1740, nodeValue1751, nodeValue3301, nodeValue4071]

noncomputable def reducedSource1238 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue858 x + ((2 : ℝ) * Sparse.eval nodeValue1626 x + ((2 : ℝ) * Sparse.eval nodeValue1740 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1238 : Integer.Sparse Master := [(Sum.inr 858, 1), (Sum.inr 1626, 2), (Sum.inr 1740, 2), (Sum.inr 1751, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1238 : Integer.Sparse.reindex keyMap MixedData.row1238 = numericRow1238 := by decide +kernel

theorem numericCheck1238 (x : Master → ℝ) : Integer.Sparse.eval numericRow1238 x =
    (1 : ℝ) * reducedSource1238 x := by
  norm_num [numericRow1238, reducedSource1238, Integer.Sparse.eval, Sparse.eval, nodeValue858, nodeValue1626, nodeValue1740, nodeValue1751, nodeValue4071]

noncomputable def reducedSource1239 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue830 x + ((2 : ℝ) * Sparse.eval nodeValue1611 x + ((1 : ℝ) * Sparse.eval nodeValue1660 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1239 : Integer.Sparse Master := [(Sum.inr 830, 1), (Sum.inr 1611, 2), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1239 : Integer.Sparse.reindex keyMap MixedData.row1239 = numericRow1239 := by decide +kernel

theorem numericCheck1239 (x : Master → ℝ) : Integer.Sparse.eval numericRow1239 x =
    (1 : ℝ) * reducedSource1239 x := by
  norm_num [numericRow1239, reducedSource1239, Integer.Sparse.eval, Sparse.eval, nodeValue830, nodeValue1611, nodeValue1660, nodeValue1738, nodeValue1740, nodeValue4071]

noncomputable def reducedSource1240 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1240 : Integer.Sparse Master := [(Sum.inr 586, 1), (Sum.inr 910, 1), (Sum.inr 950, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1240 : Integer.Sparse.reindex keyMap MixedData.row1240 = numericRow1240 := by decide +kernel

theorem numericCheck1240 (x : Master → ℝ) : Integer.Sparse.eval numericRow1240 x =
    (1 : ℝ) * reducedSource1240 x := by
  norm_num [numericRow1240, reducedSource1240, Integer.Sparse.eval, Sparse.eval, nodeValue586, nodeValue910, nodeValue950, nodeValue1026, nodeValue1041, nodeValue1044, nodeValue4083]

noncomputable def reducedSource1241 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue1338 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1241 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 1333, 1), (Sum.inr 1334, 1), (Sum.inr 1338, 1), (Sum.inr 1391, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1241 : Integer.Sparse.reindex keyMap MixedData.row1241 = numericRow1241 := by decide +kernel

theorem numericCheck1241 (x : Master → ℝ) : Integer.Sparse.eval numericRow1241 x =
    (1 : ℝ) * reducedSource1241 x := by
  norm_num [numericRow1241, reducedSource1241, Integer.Sparse.eval, Sparse.eval, nodeValue1328, nodeValue1333, nodeValue1334, nodeValue1338, nodeValue1391, nodeValue2931, nodeValue4091]

noncomputable def reducedSource1242 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue2397 x + ((1 : ℝ) * Sparse.eval nodeValue3280 x + ((1 : ℝ) * Sparse.eval nodeValue3284 x + ((2 : ℝ) * Sparse.eval nodeValue3301 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1242 : Integer.Sparse Master := [(Sum.inr 1736, 1), (Sum.inr 2397, 1), (Sum.inr 3280, 1), (Sum.inr 3284, 1), (Sum.inr 3301, 2), (Sum.inr 4071, -1)]

theorem reindexCheck1242 : Integer.Sparse.reindex keyMap MixedData.row1242 = numericRow1242 := by decide +kernel

theorem numericCheck1242 (x : Master → ℝ) : Integer.Sparse.eval numericRow1242 x =
    (1 : ℝ) * reducedSource1242 x := by
  norm_num [numericRow1242, reducedSource1242, Integer.Sparse.eval, Sparse.eval, nodeValue1736, nodeValue2397, nodeValue3280, nodeValue3284, nodeValue3301, nodeValue4071]

noncomputable def reducedSource1243 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue848 x + ((1 : ℝ) * Sparse.eval nodeValue1614 x + ((2 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1751 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1243 : Integer.Sparse Master := [(Sum.inr 848, 1), (Sum.inr 1736, 2), (Sum.inr 1751, 2), (Sum.inr 4071, -1)]

theorem reindexCheck1243 : Integer.Sparse.reindex keyMap MixedData.row1243 = numericRow1243 := by decide +kernel

theorem numericCheck1243 (x : Master → ℝ) : Integer.Sparse.eval numericRow1243 x =
    (1 : ℝ) * reducedSource1243 x := by
  norm_num [numericRow1243, reducedSource1243, Integer.Sparse.eval, Sparse.eval, nodeValue848, nodeValue1614, nodeValue1736, nodeValue1751, nodeValue4071]

noncomputable def reducedSource1244 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue823 x + ((1 : ℝ) * Sparse.eval nodeValue1606 x + ((1 : ℝ) * Sparse.eval nodeValue1655 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1738 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1244 : Integer.Sparse Master := [(Sum.inr 823, 1), (Sum.inr 1606, 1), (Sum.inr 1655, 1), (Sum.inr 1736, 1), (Sum.inr 1738, 2), (Sum.inr 4071, -1)]

theorem reindexCheck1244 : Integer.Sparse.reindex keyMap MixedData.row1244 = numericRow1244 := by decide +kernel

theorem numericCheck1244 (x : Master → ℝ) : Integer.Sparse.eval numericRow1244 x =
    (1 : ℝ) * reducedSource1244 x := by
  norm_num [numericRow1244, reducedSource1244, Integer.Sparse.eval, Sparse.eval, nodeValue823, nodeValue1606, nodeValue1655, nodeValue1736, nodeValue1738, nodeValue4071]

noncomputable def reducedSource1245 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1356 x + ((1 : ℝ) * Sparse.eval nodeValue2856 x + ((1 : ℝ) * Sparse.eval nodeValue2911 x + ((1 : ℝ) * Sparse.eval nodeValue2970 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1245 : Integer.Sparse Master := [(Sum.inr 1356, 1), (Sum.inr 2856, 1), (Sum.inr 2911, 1), (Sum.inr 2970, 1), (Sum.inr 3025, 2), (Sum.inr 4088, -1)]

theorem reindexCheck1245 : Integer.Sparse.reindex keyMap MixedData.row1245 = numericRow1245 := by decide +kernel

theorem numericCheck1245 (x : Master → ℝ) : Integer.Sparse.eval numericRow1245 x =
    (1 : ℝ) * reducedSource1245 x := by
  norm_num [numericRow1245, reducedSource1245, Integer.Sparse.eval, Sparse.eval, nodeValue1356, nodeValue2856, nodeValue2911, nodeValue2970, nodeValue3025, nodeValue4088]

noncomputable def reducedSource1246 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1133 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1146 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1246 : Integer.Sparse Master := [(Sum.inr 1133, 2), (Sum.inr 1143, 1), (Sum.inr 1146, 1), (Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1246 : Integer.Sparse.reindex keyMap MixedData.row1246 = numericRow1246 := by decide +kernel

theorem numericCheck1246 (x : Master → ℝ) : Integer.Sparse.eval numericRow1246 x =
    (1 : ℝ) * reducedSource1246 x := by
  norm_num [numericRow1246, reducedSource1246, Integer.Sparse.eval, Sparse.eval, nodeValue1133, nodeValue1143, nodeValue1146, nodeValue1245, nodeValue2522, nodeValue4084]

noncomputable def reducedSource1247 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue653 x + ((2 : ℝ) * Sparse.eval nodeValue1171 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1247 : Integer.Sparse Master := [(Sum.inr 653, 1), (Sum.inr 1171, 2), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 1306, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1247 : Integer.Sparse.reindex keyMap MixedData.row1247 = numericRow1247 := by decide +kernel

theorem numericCheck1247 (x : Master → ℝ) : Integer.Sparse.eval numericRow1247 x =
    (1 : ℝ) * reducedSource1247 x := by
  norm_num [numericRow1247, reducedSource1247, Integer.Sparse.eval, Sparse.eval, nodeValue653, nodeValue1171, nodeValue1273, nodeValue1294, nodeValue1306, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
