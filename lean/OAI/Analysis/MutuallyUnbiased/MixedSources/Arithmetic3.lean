import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource48 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2040 x + ((1 : ℝ) * Sparse.eval nodeValue2041 x + ((1 : ℝ) * Sparse.eval nodeValue2042 x + ((2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow48 : Integer.Sparse Master := [(Sum.inr 2040, 1), (Sum.inr 2041, 1), (Sum.inr 2042, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

theorem reindexCheck48 : Integer.Sparse.reindex keyMap MixedData.row48 = numericRow48 := by decide +kernel

theorem numericCheck48 (x : Master → ℝ) : Integer.Sparse.eval numericRow48 x =
    (1 : ℝ) * reducedSource48 x := by
  norm_num [numericRow48, reducedSource48, Integer.Sparse.eval, Sparse.eval, nodeValue2040, nodeValue2041, nodeValue2042, nodeValue2055, nodeValue2284, nodeValue4085]

noncomputable def reducedSource49 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1068 x + ((2 : ℝ) * Sparse.eval nodeValue2042 x + ((2 : ℝ) * Sparse.eval nodeValue2284 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

def numericRow49 : Integer.Sparse Master := [(Sum.inr 1068, 2), (Sum.inr 2042, 2), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

theorem reindexCheck49 : Integer.Sparse.reindex keyMap MixedData.row49 = numericRow49 := by decide +kernel

theorem numericCheck49 (x : Master → ℝ) : Integer.Sparse.eval numericRow49 x =
    (1 : ℝ) * reducedSource49 x := by
  norm_num [numericRow49, reducedSource49, Integer.Sparse.eval, Sparse.eval, nodeValue1068, nodeValue2042, nodeValue2284, nodeValue4085]

noncomputable def reducedSource50 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((3 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow50 : Integer.Sparse Master := [(Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 3158, 3), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

theorem reindexCheck50 : Integer.Sparse.reindex keyMap MixedData.row50 = numericRow50 := by decide +kernel

theorem numericCheck50 (x : Master → ℝ) : Integer.Sparse.eval numericRow50 x =
    (1 : ℝ) * reducedSource50 x := by
  norm_num [numericRow50, reducedSource50, Integer.Sparse.eval, Sparse.eval, nodeValue2235, nodeValue3155, nodeValue3158, nodeValue3619, nodeValue4083]

noncomputable def reducedSource51 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1014 x + ((1 : ℝ) * Sparse.eval nodeValue1016 x + ((3 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow51 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1016, 1), (Sum.inr 1024, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

theorem reindexCheck51 : Integer.Sparse.reindex keyMap MixedData.row51 = numericRow51 := by decide +kernel

theorem numericCheck51 (x : Master → ℝ) : Integer.Sparse.eval numericRow51 x =
    (1 : ℝ) * reducedSource51 x := by
  norm_num [numericRow51, reducedSource51, Integer.Sparse.eval, Sparse.eval, nodeValue1014, nodeValue1016, nodeValue1024, nodeValue2235, nodeValue4083]

noncomputable def reducedSource52 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1014 x + ((3 : ℝ) * Sparse.eval nodeValue2083 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow52 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 2083, 3), (Sum.inr 2233, 1), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

theorem reindexCheck52 : Integer.Sparse.reindex keyMap MixedData.row52 = numericRow52 := by decide +kernel

theorem numericCheck52 (x : Master → ℝ) : Integer.Sparse.eval numericRow52 x =
    (1 : ℝ) * reducedSource52 x := by
  norm_num [numericRow52, reducedSource52, Integer.Sparse.eval, Sparse.eval, nodeValue1014, nodeValue2083, nodeValue2233, nodeValue2235, nodeValue4083]

noncomputable def reducedSource53 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1457 x + ((3 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow53 : Integer.Sparse Master := [(Sum.inr 1457, 1), (Sum.inr 2010, 3), (Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 4083, -1)]

theorem reindexCheck53 : Integer.Sparse.reindex keyMap MixedData.row53 = numericRow53 := by decide +kernel

theorem numericCheck53 (x : Master → ℝ) : Integer.Sparse.eval numericRow53 x =
    (1 : ℝ) * reducedSource53 x := by
  norm_num [numericRow53, reducedSource53, Integer.Sparse.eval, Sparse.eval, nodeValue1457, nodeValue2010, nodeValue2235, nodeValue3155, nodeValue4083]

noncomputable def reducedSource54 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue2010 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow54 : Integer.Sparse Master := [(Sum.inr 1024, 1), (Sum.inr 2010, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

theorem reindexCheck54 : Integer.Sparse.reindex keyMap MixedData.row54 = numericRow54 := by decide +kernel

theorem numericCheck54 (x : Master → ℝ) : Integer.Sparse.eval numericRow54 x =
    (1 : ℝ) * reducedSource54 x := by
  norm_num [numericRow54, reducedSource54, Integer.Sparse.eval, Sparse.eval, nodeValue1024, nodeValue2010, nodeValue2092, nodeValue2235, nodeValue2245, nodeValue4083]

noncomputable def reducedSource55 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1460 x + ((1 : ℝ) * Sparse.eval nodeValue2083 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow55 : Integer.Sparse Master := [(Sum.inr 1460, 1), (Sum.inr 2083, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 3158, 1), (Sum.inr 4083, -1)]

theorem reindexCheck55 : Integer.Sparse.reindex keyMap MixedData.row55 = numericRow55 := by decide +kernel

theorem numericCheck55 (x : Master → ℝ) : Integer.Sparse.eval numericRow55 x =
    (1 : ℝ) * reducedSource55 x := by
  norm_num [numericRow55, reducedSource55, Integer.Sparse.eval, Sparse.eval, nodeValue1460, nodeValue2083, nodeValue2092, nodeValue2235, nodeValue3158, nodeValue4083]

noncomputable def reducedSource56 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1016 x + ((1 : ℝ) * Sparse.eval nodeValue1457 x + ((3 : ℝ) * Sparse.eval nodeValue1460 x + ((1 : ℝ) * Sparse.eval nodeValue2235 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow56 : Integer.Sparse Master := [(Sum.inr 1016, 1), (Sum.inr 1457, 1), (Sum.inr 1460, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

theorem reindexCheck56 : Integer.Sparse.reindex keyMap MixedData.row56 = numericRow56 := by decide +kernel

theorem numericCheck56 (x : Master → ℝ) : Integer.Sparse.eval numericRow56 x =
    (1 : ℝ) * reducedSource56 x := by
  norm_num [numericRow56, reducedSource56, Integer.Sparse.eval, Sparse.eval, nodeValue1016, nodeValue1457, nodeValue1460, nodeValue2235, nodeValue4083]

noncomputable def reducedSource57 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1078 x + ((1 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue2283 x + ((3 : ℝ) * Sparse.eval nodeValue2290 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow57 : Integer.Sparse Master := [(Sum.inr 1078, 1), (Sum.inr 2050, 1), (Sum.inr 2283, 1), (Sum.inr 2290, 3), (Sum.inr 4085, -1)]

theorem reindexCheck57 : Integer.Sparse.reindex keyMap MixedData.row57 = numericRow57 := by decide +kernel

theorem numericCheck57 (x : Master → ℝ) : Integer.Sparse.eval numericRow57 x =
    (1 : ℝ) * reducedSource57 x := by
  norm_num [numericRow57, reducedSource57, Integer.Sparse.eval, Sparse.eval, nodeValue1078, nodeValue2050, nodeValue2283, nodeValue2290, nodeValue4085]

noncomputable def reducedSource58 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue994 x + ((1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((2 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue1191 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((2 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((2 : ℝ) * Sparse.eval nodeValue2454 x + ((2 : ℝ) * Sparse.eval nodeValue2465 x + ((2 : ℝ) * Sparse.eval nodeValue2495 x + ((2 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2640 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

def numericRow58 : Integer.Sparse Master := [(Sum.inl 0, -236), (Sum.inl 6, -20), (Sum.inl 2, 180), (Sum.inl 3, 1280), (Sum.inl 13, 320), (Sum.inl 52, 320), (Sum.inl 12, 640), (Sum.inl 1, -60), (Sum.inr 991, 17280), (Sum.inr 994, 8640), (Sum.inr 1010, 8640), (Sum.inr 1059, 8640), (Sum.inr 1181, 17280), (Sum.inr 1191, 8640), (Sum.inr 1264, 8640), (Sum.inr 2393, 17280), (Sum.inr 2408, 8640), (Sum.inr 2454, 17280), (Sum.inr 2465, 17280), (Sum.inr 2495, 17280), (Sum.inr 2618, 17280), (Sum.inr 2732, 17280), (Sum.inr 2744, 8640), (Sum.inr 3039, 17280), (Sum.inr 3055, 8640)]

theorem reindexCheck58 : Integer.Sparse.reindex keyMap MixedData.row58 = numericRow58 := by decide +kernel

theorem numericCheck58 (x : Master → ℝ) : Integer.Sparse.eval numericRow58 x =
    (8640 : ℝ) * reducedSource58 x := by
  norm_num [numericRow58, reducedSource58, Integer.Sparse.eval, Sparse.eval, nodeValue991, nodeValue994, nodeValue1010, nodeValue1059, nodeValue1181, nodeValue1191, nodeValue1264, nodeValue2393, nodeValue2408, nodeValue2454, nodeValue2465, nodeValue2495, nodeValue2618, nodeValue2640, nodeValue2732, nodeValue2744, nodeValue2776, nodeValue3039, nodeValue3055, nodeValue3110, nodeValue3889]
  ring

noncomputable def reducedSource59 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1629 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((2 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((2 : ℝ) * Sparse.eval nodeValue3358 x + ((2 : ℝ) * Sparse.eval nodeValue3437 x + ((2 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0))))))))))))))))))))

def numericRow59 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -50), (Sum.inr 1624, 4320), (Sum.inr 1628, 2160), (Sum.inr 1629, 2160), (Sum.inr 1729, 2160), (Sum.inr 2837, 4320), (Sum.inr 2842, 2160), (Sum.inr 3052, 2160), (Sum.inr 3242, 4320), (Sum.inr 3247, 2160), (Sum.inr 3302, 2160), (Sum.inr 3358, 4320), (Sum.inr 3437, 4320), (Sum.inr 3472, 4320), (Sum.inr 3486, 2160), (Sum.inr 3523, 4320), (Sum.inr 3535, 4320), (Sum.inr 3541, 4320), (Sum.inr 3548, 2160), (Sum.inr 3584, 2160), (Sum.inr 3626, 2160)]

theorem reindexCheck59 : Integer.Sparse.reindex keyMap MixedData.row59 = numericRow59 := by decide +kernel

theorem numericCheck59 (x : Master → ℝ) : Integer.Sparse.eval numericRow59 x =
    (2160 : ℝ) * reducedSource59 x := by
  norm_num [numericRow59, reducedSource59, Integer.Sparse.eval, Sparse.eval, nodeValue1624, nodeValue1628, nodeValue1629, nodeValue1729, nodeValue2837, nodeValue2842, nodeValue3052, nodeValue3242, nodeValue3247, nodeValue3302, nodeValue3358, nodeValue3437, nodeValue3472, nodeValue3486, nodeValue3523, nodeValue3535, nodeValue3541, nodeValue3548, nodeValue3584, nodeValue3626, nodeValue3862]
  ring

noncomputable def reducedSource60 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow60 : Integer.Sparse Master := [(Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 2), (Sum.inr 3054, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem reindexCheck60 : Integer.Sparse.reindex keyMap MixedData.row60 = numericRow60 := by decide +kernel

theorem numericCheck60 (x : Master → ℝ) : Integer.Sparse.eval numericRow60 x =
    (1 : ℝ) * reducedSource60 x := by
  norm_num [numericRow60, reducedSource60, Integer.Sparse.eval, Sparse.eval, nodeValue2734, nodeValue2777, nodeValue3038, nodeValue3054, nodeValue3907, nodeValue4092]

noncomputable def reducedSource61 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1224 x + ((1 : ℝ) * Sparse.eval nodeValue1227 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1279 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow61 : Integer.Sparse Master := [(Sum.inr 1224, 2), (Sum.inr 1227, 1), (Sum.inr 1243, 1), (Sum.inr 1279, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

theorem reindexCheck61 : Integer.Sparse.reindex keyMap MixedData.row61 = numericRow61 := by decide +kernel

theorem numericCheck61 (x : Master → ℝ) : Integer.Sparse.eval numericRow61 x =
    (1 : ℝ) * reducedSource61 x := by
  norm_num [numericRow61, reducedSource61, Integer.Sparse.eval, Sparse.eval, nodeValue1224, nodeValue1227, nodeValue1243, nodeValue1279, nodeValue2734, nodeValue4092]

noncomputable def reducedSource62 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1279 x + ((2 : ℝ) * Sparse.eval nodeValue2579 x + ((1 : ℝ) * Sparse.eval nodeValue2651 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow62 : Integer.Sparse Master := [(Sum.inr 1279, 1), (Sum.inr 2579, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

theorem reindexCheck62 : Integer.Sparse.reindex keyMap MixedData.row62 = numericRow62 := by decide +kernel

theorem numericCheck62 (x : Master → ℝ) : Integer.Sparse.eval numericRow62 x =
    (1 : ℝ) * reducedSource62 x := by
  norm_num [numericRow62, reducedSource62, Integer.Sparse.eval, Sparse.eval, nodeValue1279, nodeValue2579, nodeValue2651, nodeValue2734, nodeValue2774, nodeValue4092]

noncomputable def reducedSource63 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1372 x + ((2 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow63 : Integer.Sparse Master := [(Sum.inr 1372, 1), (Sum.inr 2495, 2), (Sum.inr 2519, 1), (Sum.inr 2734, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem reindexCheck63 : Integer.Sparse.reindex keyMap MixedData.row63 = numericRow63 := by decide +kernel

theorem numericCheck63 (x : Master → ℝ) : Integer.Sparse.eval numericRow63 x =
    (1 : ℝ) * reducedSource63 x := by
  norm_num [numericRow63, reducedSource63, Integer.Sparse.eval, Sparse.eval, nodeValue1372, nodeValue2495, nodeValue2519, nodeValue2734, nodeValue3054, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
