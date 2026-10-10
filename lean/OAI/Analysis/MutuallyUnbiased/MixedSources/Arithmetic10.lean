import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource160 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow160 : Integer.Sparse Master := [(Sum.inr 1042, 1), (Sum.inr 2021, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 2262, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

theorem reindexCheck160 : Integer.Sparse.reindex keyMap MixedData.row160 = numericRow160 := by decide +kernel

theorem numericCheck160 (x : Master → ℝ) : Integer.Sparse.eval numericRow160 x =
    (1 : ℝ) * reducedSource160 x := by
  norm_num [numericRow160, reducedSource160, Integer.Sparse.eval, Sparse.eval, nodeValue1042, nodeValue2021, nodeValue2108, nodeValue2253, nodeValue2262, nodeValue2266, nodeValue4084]

noncomputable def reducedSource161 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2124 x + ((1 : ℝ) * Sparse.eval nodeValue2125 x + ((1 : ℝ) * Sparse.eval nodeValue2126 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow161 : Integer.Sparse Master := [(Sum.inr 2124, 1), (Sum.inr 2125, 1), (Sum.inr 2126, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 4084, -1)]

theorem reindexCheck161 : Integer.Sparse.reindex keyMap MixedData.row161 = numericRow161 := by decide +kernel

theorem numericCheck161 (x : Master → ℝ) : Integer.Sparse.eval numericRow161 x =
    (1 : ℝ) * reducedSource161 x := by
  norm_num [numericRow161, reducedSource161, Integer.Sparse.eval, Sparse.eval, nodeValue2124, nodeValue2125, nodeValue2126, nodeValue2133, nodeValue2253, nodeValue2513, nodeValue4084]

noncomputable def reducedSource162 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1030 x + ((1 : ℝ) * Sparse.eval nodeValue2014 x + ((1 : ℝ) * Sparse.eval nodeValue2097 x + ((1 : ℝ) * Sparse.eval nodeValue2126 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow162 : Integer.Sparse Master := [(Sum.inr 1030, 1), (Sum.inr 2014, 1), (Sum.inr 2097, 1), (Sum.inr 2126, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

theorem reindexCheck162 : Integer.Sparse.reindex keyMap MixedData.row162 = numericRow162 := by decide +kernel

theorem numericCheck162 (x : Master → ℝ) : Integer.Sparse.eval numericRow162 x =
    (1 : ℝ) * reducedSource162 x := by
  norm_num [numericRow162, reducedSource162, Integer.Sparse.eval, Sparse.eval, nodeValue1030, nodeValue2014, nodeValue2097, nodeValue2126, nodeValue2253, nodeValue4084]

noncomputable def reducedSource163 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue793 x + ((1 : ℝ) * Sparse.eval nodeValue794 x + ((1 : ℝ) * Sparse.eval nodeValue796 x + ((1 : ℝ) * Sparse.eval nodeValue808 x + ((1 : ℝ) * Sparse.eval nodeValue825 x + ((1 : ℝ) * Sparse.eval nodeValue1902 x + ((1 : ℝ) * Sparse.eval nodeValue1904 x + ((1 : ℝ) * Sparse.eval nodeValue1910 x + ((1 : ℝ) * Sparse.eval nodeValue1923 x + ((1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2108 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + 0)))))))))))))))))))))))))))))

def numericRow163 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 2, -50), (Sum.inl 3, -400), (Sum.inl 13, -240), (Sum.inl 12, -160), (Sum.inl 4, -80), (Sum.inl 1, 70), (Sum.inr 793, 4320), (Sum.inr 794, 4320), (Sum.inr 796, 4320), (Sum.inr 808, 4320), (Sum.inr 825, 4320), (Sum.inr 1902, 4320), (Sum.inr 1904, 4320), (Sum.inr 1910, 4320), (Sum.inr 1923, 4320), (Sum.inr 2034, 4320), (Sum.inr 2035, 4320), (Sum.inr 2039, 4320), (Sum.inr 2055, 4320), (Sum.inr 2089, 4320), (Sum.inr 2090, 4320), (Sum.inr 2094, 4320), (Sum.inr 2108, 4320), (Sum.inr 2196, 4320), (Sum.inr 2197, 4320), (Sum.inr 2207, 4320), (Sum.inr 2217, 4320), (Sum.inr 2250, 4320), (Sum.inr 2251, 4320), (Sum.inr 2259, 4320), (Sum.inr 2274, 4320), (Sum.inr 3803, 4320), (Sum.inr 3813, 4320), (Sum.inr 3814, 4320)]

theorem reindexCheck163 : Integer.Sparse.reindex keyMap MixedData.row163 = numericRow163 := by decide +kernel

theorem numericCheck163 (x : Master → ℝ) : Integer.Sparse.eval numericRow163 x =
    (4320 : ℝ) * reducedSource163 x := by
  norm_num [numericRow163, reducedSource163, Integer.Sparse.eval, Sparse.eval, nodeValue793, nodeValue794, nodeValue796, nodeValue808, nodeValue825, nodeValue1902, nodeValue1904, nodeValue1910, nodeValue1923, nodeValue2034, nodeValue2035, nodeValue2039, nodeValue2055, nodeValue2089, nodeValue2090, nodeValue2094, nodeValue2108, nodeValue2196, nodeValue2197, nodeValue2207, nodeValue2217, nodeValue2250, nodeValue2251, nodeValue2259, nodeValue2274, nodeValue3803, nodeValue3813, nodeValue3814, nodeValue3856, nodeValue3883]
  ring

noncomputable def reducedSource164 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

def numericRow164 : Integer.Sparse Master := [(Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 3809, 2), (Sum.inr 3814, 2), (Sum.inr 4092, -1)]

theorem reindexCheck164 : Integer.Sparse.reindex keyMap MixedData.row164 = numericRow164 := by decide +kernel

theorem numericCheck164 (x : Master → ℝ) : Integer.Sparse.eval numericRow164 x =
    (1 : ℝ) * reducedSource164 x := by
  norm_num [numericRow164, reducedSource164, Integer.Sparse.eval, Sparse.eval, nodeValue3222, nodeValue3803, nodeValue3809, nodeValue3814, nodeValue4092]

noncomputable def reducedSource165 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1463 x + ((2 : ℝ) * Sparse.eval nodeValue1465 x + ((2 : ℝ) * Sparse.eval nodeValue1466 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

def numericRow165 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 1465, 2), (Sum.inr 1466, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem reindexCheck165 : Integer.Sparse.reindex keyMap MixedData.row165 = numericRow165 := by decide +kernel

theorem numericCheck165 (x : Master → ℝ) : Integer.Sparse.eval numericRow165 x =
    (1 : ℝ) * reducedSource165 x := by
  norm_num [numericRow165, reducedSource165, Integer.Sparse.eval, Sparse.eval, nodeValue1463, nodeValue1465, nodeValue1466, nodeValue3222, nodeValue4092]

noncomputable def reducedSource166 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1463 x + ((2 : ℝ) * Sparse.eval nodeValue3170 x + ((2 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

def numericRow166 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 3170, 2), (Sum.inr 3196, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem reindexCheck166 : Integer.Sparse.reindex keyMap MixedData.row166 = numericRow166 := by decide +kernel

theorem numericCheck166 (x : Master → ℝ) : Integer.Sparse.eval numericRow166 x =
    (1 : ℝ) * reducedSource166 x := by
  norm_num [numericRow166, reducedSource166, Integer.Sparse.eval, Sparse.eval, nodeValue1463, nodeValue3170, nodeValue3196, nodeValue3222, nodeValue4092]

noncomputable def reducedSource167 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2474 x + ((2 : ℝ) * Sparse.eval nodeValue3217 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3803 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

def numericRow167 : Integer.Sparse Master := [(Sum.inr 2474, 2), (Sum.inr 3217, 2), (Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

theorem reindexCheck167 : Integer.Sparse.reindex keyMap MixedData.row167 = numericRow167 := by decide +kernel

theorem numericCheck167 (x : Master → ℝ) : Integer.Sparse.eval numericRow167 x =
    (1 : ℝ) * reducedSource167 x := by
  norm_num [numericRow167, reducedSource167, Integer.Sparse.eval, Sparse.eval, nodeValue2474, nodeValue3217, nodeValue3222, nodeValue3803, nodeValue4092]

noncomputable def reducedSource168 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1466 x + ((1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3217 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow168 : Integer.Sparse Master := [(Sum.inr 1466, 1), (Sum.inr 3174, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3217, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem reindexCheck168 : Integer.Sparse.reindex keyMap MixedData.row168 = numericRow168 := by decide +kernel

theorem numericCheck168 (x : Master → ℝ) : Integer.Sparse.eval numericRow168 x =
    (1 : ℝ) * reducedSource168 x := by
  norm_num [numericRow168, reducedSource168, Integer.Sparse.eval, Sparse.eval, nodeValue1466, nodeValue3174, nodeValue3180, nodeValue3198, nodeValue3217, nodeValue3222, nodeValue4092]

noncomputable def reducedSource169 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow169 : Integer.Sparse Master := [(Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3196, 1), (Sum.inr 3198, 1), (Sum.inr 3222, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem reindexCheck169 : Integer.Sparse.reindex keyMap MixedData.row169 = numericRow169 := by decide +kernel

theorem numericCheck169 (x : Master → ℝ) : Integer.Sparse.eval numericRow169 x =
    (1 : ℝ) * reducedSource169 x := by
  norm_num [numericRow169, reducedSource169, Integer.Sparse.eval, Sparse.eval, nodeValue2497, nodeValue2716, nodeValue3196, nodeValue3198, nodeValue3222, nodeValue3814, nodeValue4092]

noncomputable def reducedSource170 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1465 x + ((1 : ℝ) * Sparse.eval nodeValue2474 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue3222 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow170 : Integer.Sparse Master := [(Sum.inr 1465, 1), (Sum.inr 2474, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem reindexCheck170 : Integer.Sparse.reindex keyMap MixedData.row170 = numericRow170 := by decide +kernel

theorem numericCheck170 (x : Master → ℝ) : Integer.Sparse.eval numericRow170 x =
    (1 : ℝ) * reducedSource170 x := by
  norm_num [numericRow170, reducedSource170, Integer.Sparse.eval, Sparse.eval, nodeValue1465, nodeValue2474, nodeValue2486, nodeValue2497, nodeValue2716, nodeValue3222, nodeValue4092]

noncomputable def reducedSource171 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2233 x + ((3 : ℝ) * Sparse.eval nodeValue3567 x + ((1 : ℝ) * Sparse.eval nodeValue3618 x + ((1 : ℝ) * Sparse.eval nodeValue3619 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow171 : Integer.Sparse Master := [(Sum.inr 2233, 1), (Sum.inr 3567, 3), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

theorem reindexCheck171 : Integer.Sparse.reindex keyMap MixedData.row171 = numericRow171 := by decide +kernel

theorem numericCheck171 (x : Master → ℝ) : Integer.Sparse.eval numericRow171 x =
    (1 : ℝ) * reducedSource171 x := by
  norm_num [numericRow171, reducedSource171, Integer.Sparse.eval, Sparse.eval, nodeValue2233, nodeValue3567, nodeValue3618, nodeValue3619, nodeValue4083]

noncomputable def reducedSource172 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1014 x + ((1 : ℝ) * Sparse.eval nodeValue1015 x + ((3 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow172 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1015, 1), (Sum.inr 1021, 3), (Sum.inr 2233, 1), (Sum.inr 4083, -1)]

theorem reindexCheck172 : Integer.Sparse.reindex keyMap MixedData.row172 = numericRow172 := by decide +kernel

theorem numericCheck172 (x : Master → ℝ) : Integer.Sparse.eval numericRow172 x =
    (1 : ℝ) * reducedSource172 x := by
  norm_num [numericRow172, reducedSource172, Integer.Sparse.eval, Sparse.eval, nodeValue1014, nodeValue1015, nodeValue1021, nodeValue2233, nodeValue4083]

noncomputable def reducedSource173 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1021 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow173 : Integer.Sparse Master := [(Sum.inr 1021, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 2243, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

theorem reindexCheck173 : Integer.Sparse.reindex keyMap MixedData.row173 = numericRow173 := by decide +kernel

theorem numericCheck173 (x : Master → ℝ) : Integer.Sparse.eval numericRow173 x =
    (1 : ℝ) * reducedSource173 x := by
  norm_num [numericRow173, reducedSource173, Integer.Sparse.eval, Sparse.eval, nodeValue1021, nodeValue2089, nodeValue2233, nodeValue2243, nodeValue2245, nodeValue4083]

noncomputable def reducedSource174 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2083 x + ((1 : ℝ) * Sparse.eval nodeValue2084 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow174 : Integer.Sparse Master := [(Sum.inr 2083, 1), (Sum.inr 2084, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 3567, 1), (Sum.inr 4083, -1)]

theorem reindexCheck174 : Integer.Sparse.reindex keyMap MixedData.row174 = numericRow174 := by decide +kernel

theorem numericCheck174 (x : Master → ℝ) : Integer.Sparse.eval numericRow174 x =
    (1 : ℝ) * reducedSource174 x := by
  norm_num [numericRow174, reducedSource174, Integer.Sparse.eval, Sparse.eval, nodeValue2083, nodeValue2084, nodeValue2089, nodeValue2233, nodeValue3567, nodeValue4083]

noncomputable def reducedSource175 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1015 x + ((3 : ℝ) * Sparse.eval nodeValue2084 x + ((2 : ℝ) * Sparse.eval nodeValue2233 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))

def numericRow175 : Integer.Sparse Master := [(Sum.inr 1015, 1), (Sum.inr 2084, 3), (Sum.inr 2233, 2), (Sum.inr 4083, -1)]

theorem reindexCheck175 : Integer.Sparse.reindex keyMap MixedData.row175 = numericRow175 := by decide +kernel

theorem numericCheck175 (x : Master → ℝ) : Integer.Sparse.eval numericRow175 x =
    (1 : ℝ) * reducedSource175 x := by
  norm_num [numericRow175, reducedSource175, Integer.Sparse.eval, Sparse.eval, nodeValue1015, nodeValue2084, nodeValue2233, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
