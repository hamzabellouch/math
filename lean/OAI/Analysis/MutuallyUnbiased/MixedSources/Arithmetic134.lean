import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2144 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1690 x + ((1 : ℝ) * Sparse.eval nodeValue2184 x + ((1 : ℝ) * Sparse.eval nodeValue3255 x + ((2 : ℝ) * Sparse.eval nodeValue3264 x + ((1 : ℝ) * Sparse.eval nodeValue3273 x + ((-1 : ℝ) * Sparse.eval nodeValue4064 x + 0)))))

def numericRow2144 : Integer.Sparse Master := [(Sum.inr 1690, 1), (Sum.inr 2184, 1), (Sum.inr 3255, 1), (Sum.inr 3264, 2), (Sum.inr 3273, 1), (Sum.inr 4064, -1)]

theorem reindexCheck2144 : Integer.Sparse.reindex keyMap MixedData.row2144 = numericRow2144 := by decide +kernel

theorem numericCheck2144 (x : Master → ℝ) : Integer.Sparse.eval numericRow2144 x =
    (1 : ℝ) * reducedSource2144 x := by
  norm_num [numericRow2144, reducedSource2144, Integer.Sparse.eval, Sparse.eval, nodeValue1690, nodeValue2184, nodeValue3255, nodeValue3264, nodeValue3273, nodeValue4064]

noncomputable def reducedSource2145 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1681 x + ((1 : ℝ) * Sparse.eval nodeValue2657 x + ((1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3265 x + ((2 : ℝ) * Sparse.eval nodeValue3270 x + ((-1 : ℝ) * Sparse.eval nodeValue4065 x + 0)))))

def numericRow2145 : Integer.Sparse Master := [(Sum.inr 1681, 1), (Sum.inr 2657, 1), (Sum.inr 3258, 1), (Sum.inr 3265, 1), (Sum.inr 3270, 2), (Sum.inr 4065, -1)]

theorem reindexCheck2145 : Integer.Sparse.reindex keyMap MixedData.row2145 = numericRow2145 := by decide +kernel

theorem numericCheck2145 (x : Master → ℝ) : Integer.Sparse.eval numericRow2145 x =
    (1 : ℝ) * reducedSource2145 x := by
  norm_num [numericRow2145, reducedSource2145, Integer.Sparse.eval, Sparse.eval, nodeValue1681, nodeValue2657, nodeValue3258, nodeValue3265, nodeValue3270, nodeValue4065]

noncomputable def reducedSource2146 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1691 x + ((1 : ℝ) * Sparse.eval nodeValue3261 x + ((2 : ℝ) * Sparse.eval nodeValue3265 x + ((2 : ℝ) * Sparse.eval nodeValue3274 x + ((-1 : ℝ) * Sparse.eval nodeValue4065 x + 0))))

def numericRow2146 : Integer.Sparse Master := [(Sum.inr 1691, 1), (Sum.inr 3261, 1), (Sum.inr 3265, 2), (Sum.inr 3274, 2), (Sum.inr 4065, -1)]

theorem reindexCheck2146 : Integer.Sparse.reindex keyMap MixedData.row2146 = numericRow2146 := by decide +kernel

theorem numericCheck2146 (x : Master → ℝ) : Integer.Sparse.eval numericRow2146 x =
    (1 : ℝ) * reducedSource2146 x := by
  norm_num [numericRow2146, reducedSource2146, Integer.Sparse.eval, Sparse.eval, nodeValue1691, nodeValue3261, nodeValue3265, nodeValue3274, nodeValue4065]

noncomputable def reducedSource2147 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2161 x + ((2 : ℝ) * Sparse.eval nodeValue2163 x + ((2 : ℝ) * Sparse.eval nodeValue2169 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))

def numericRow2147 : Integer.Sparse Master := [(Sum.inr 2161, 2), (Sum.inr 2163, 2), (Sum.inr 2169, 2), (Sum.inr 4076, -1)]

theorem reindexCheck2147 : Integer.Sparse.reindex keyMap MixedData.row2147 = numericRow2147 := by decide +kernel

theorem numericCheck2147 (x : Master → ℝ) : Integer.Sparse.eval numericRow2147 x =
    (1 : ℝ) * reducedSource2147 x := by
  norm_num [numericRow2147, reducedSource2147, Integer.Sparse.eval, Sparse.eval, nodeValue2161, nodeValue2163, nodeValue2169, nodeValue4076]

noncomputable def reducedSource2148 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2159 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))))

def numericRow2148 : Integer.Sparse Master := [(Sum.inr 2155, 2), (Sum.inr 2159, 1), (Sum.inr 2168, 1), (Sum.inr 2273, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

theorem reindexCheck2148 : Integer.Sparse.reindex keyMap MixedData.row2148 = numericRow2148 := by decide +kernel

theorem numericCheck2148 (x : Master → ℝ) : Integer.Sparse.eval numericRow2148 x =
    (1 : ℝ) * reducedSource2148 x := by
  norm_num [numericRow2148, reducedSource2148, Integer.Sparse.eval, Sparse.eval, nodeValue2155, nodeValue2159, nodeValue2168, nodeValue2273, nodeValue3596, nodeValue4076]

noncomputable def reducedSource2149 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))))

def numericRow2149 : Integer.Sparse Master := [(Sum.inr 2164, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2286, 1), (Sum.inr 3423, 1), (Sum.inr 4076, -1)]

theorem reindexCheck2149 : Integer.Sparse.reindex keyMap MixedData.row2149 = numericRow2149 := by decide +kernel

theorem numericCheck2149 (x : Master → ℝ) : Integer.Sparse.eval numericRow2149 x =
    (1 : ℝ) * reducedSource2149 x := by
  norm_num [numericRow2149, reducedSource2149, Integer.Sparse.eval, Sparse.eval, nodeValue2164, nodeValue2168, nodeValue2169, nodeValue2286, nodeValue3423, nodeValue4076]

noncomputable def reducedSource2150 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2168 x + ((2 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3422 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))))

def numericRow2150 : Integer.Sparse Master := [(Sum.inr 2168, 1), (Sum.inr 3415, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

theorem reindexCheck2150 : Integer.Sparse.reindex keyMap MixedData.row2150 = numericRow2150 := by decide +kernel

theorem numericCheck2150 (x : Master → ℝ) : Integer.Sparse.eval numericRow2150 x =
    (1 : ℝ) * reducedSource2150 x := by
  norm_num [numericRow2150, reducedSource2150, Integer.Sparse.eval, Sparse.eval, nodeValue2168, nodeValue3415, nodeValue3422, nodeValue3423, nodeValue3596, nodeValue4076]

noncomputable def reducedSource2151 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3419 x + ((2 : ℝ) * Sparse.eval nodeValue3422 x + ((2 : ℝ) * Sparse.eval nodeValue3423 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))

def numericRow2151 : Integer.Sparse Master := [(Sum.inr 3419, 2), (Sum.inr 3422, 2), (Sum.inr 3423, 2), (Sum.inr 4076, -1)]

theorem reindexCheck2151 : Integer.Sparse.reindex keyMap MixedData.row2151 = numericRow2151 := by decide +kernel

theorem numericCheck2151 (x : Master → ℝ) : Integer.Sparse.eval numericRow2151 x =
    (1 : ℝ) * reducedSource2151 x := by
  norm_num [numericRow2151, reducedSource2151, Integer.Sparse.eval, Sparse.eval, nodeValue3419, nodeValue3422, nodeValue3423, nodeValue4076]

noncomputable def reducedSource2152 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2169 x + ((2 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3512 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))

def numericRow2152 : Integer.Sparse Master := [(Sum.inr 2169, 2), (Sum.inr 3423, 2), (Sum.inr 3512, 2), (Sum.inr 4076, -1)]

theorem reindexCheck2152 : Integer.Sparse.reindex keyMap MixedData.row2152 = numericRow2152 := by decide +kernel

theorem numericCheck2152 (x : Master → ℝ) : Integer.Sparse.eval numericRow2152 x =
    (1 : ℝ) * reducedSource2152 x := by
  norm_num [numericRow2152, reducedSource2152, Integer.Sparse.eval, Sparse.eval, nodeValue2169, nodeValue3423, nodeValue3512, nodeValue4076]

noncomputable def reducedSource2153 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2256 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0))))))

def numericRow2153 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2151, 1), (Sum.inr 2153, 1), (Sum.inr 2165, 1), (Sum.inr 2256, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2153 : Integer.Sparse.reindex keyMap MixedData.row2153 = numericRow2153 := by decide +kernel

theorem numericCheck2153 (x : Master → ℝ) : Integer.Sparse.eval numericRow2153 x =
    (1 : ℝ) * reducedSource2153 x := by
  norm_num [numericRow2153, reducedSource2153, Integer.Sparse.eval, Sparse.eval, nodeValue2147, nodeValue2151, nodeValue2153, nodeValue2165, nodeValue2256, nodeValue3457, nodeValue4074]

noncomputable def reducedSource2154 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2160 x + ((2 : ℝ) * Sparse.eval nodeValue2162 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2180 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

def numericRow2154 : Integer.Sparse Master := [(Sum.inr 2160, 1), (Sum.inr 2162, 2), (Sum.inr 2165, 1), (Sum.inr 2180, 1), (Sum.inr 2186, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2154 : Integer.Sparse.reindex keyMap MixedData.row2154 = numericRow2154 := by decide +kernel

theorem numericCheck2154 (x : Master → ℝ) : Integer.Sparse.eval numericRow2154 x =
    (1 : ℝ) * reducedSource2154 x := by
  norm_num [numericRow2154, reducedSource2154, Integer.Sparse.eval, Sparse.eval, nodeValue2160, nodeValue2162, nodeValue2165, nodeValue2180, nodeValue2186, nodeValue4074]

noncomputable def reducedSource2155 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2140 x + ((1 : ℝ) * Sparse.eval nodeValue2143 x + ((2 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2239 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

def numericRow2155 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2143, 1), (Sum.inr 2151, 2), (Sum.inr 2239, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2155 : Integer.Sparse.reindex keyMap MixedData.row2155 = numericRow2155 := by decide +kernel

theorem numericCheck2155 (x : Master → ℝ) : Integer.Sparse.eval numericRow2155 x =
    (1 : ℝ) * reducedSource2155 x := by
  norm_num [numericRow2155, reducedSource2155, Integer.Sparse.eval, Sparse.eval, nodeValue2140, nodeValue2143, nodeValue2151, nodeValue2239, nodeValue3588, nodeValue4074]

noncomputable def reducedSource2156 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3408 x + ((2 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

def numericRow2156 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3411, 2), (Sum.inr 3413, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2156 : Integer.Sparse.reindex keyMap MixedData.row2156 = numericRow2156 := by decide +kernel

theorem numericCheck2156 (x : Master → ℝ) : Integer.Sparse.eval numericRow2156 x =
    (1 : ℝ) * reducedSource2156 x := by
  norm_num [numericRow2156, reducedSource2156, Integer.Sparse.eval, Sparse.eval, nodeValue3408, nodeValue3411, nodeValue3413, nodeValue3420, nodeValue3457, nodeValue4074]

noncomputable def reducedSource2157 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2181 x + ((1 : ℝ) * Sparse.eval nodeValue2185 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2223 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

def numericRow2157 : Integer.Sparse Master := [(Sum.inr 2181, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2223, 2), (Sum.inr 3420, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2157 : Integer.Sparse.reindex keyMap MixedData.row2157 = numericRow2157 := by decide +kernel

theorem numericCheck2157 (x : Master → ℝ) : Integer.Sparse.eval numericRow2157 x =
    (1 : ℝ) * reducedSource2157 x := by
  norm_num [numericRow2157, reducedSource2157, Integer.Sparse.eval, Sparse.eval, nodeValue2181, nodeValue2185, nodeValue2186, nodeValue2223, nodeValue3420, nodeValue4074]

noncomputable def reducedSource2158 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2185 x + ((1 : ℝ) * Sparse.eval nodeValue3403 x + ((2 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

def numericRow2158 : Integer.Sparse Master := [(Sum.inr 2185, 1), (Sum.inr 3411, 2), (Sum.inr 3420, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2158 : Integer.Sparse.reindex keyMap MixedData.row2158 = numericRow2158 := by decide +kernel

theorem numericCheck2158 (x : Master → ℝ) : Integer.Sparse.eval numericRow2158 x =
    (1 : ℝ) * reducedSource2158 x := by
  norm_num [numericRow2158, reducedSource2158, Integer.Sparse.eval, Sparse.eval, nodeValue2185, nodeValue3403, nodeValue3411, nodeValue3420, nodeValue3588, nodeValue4074]

noncomputable def reducedSource2159 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2143 x + ((1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2185 x + ((2 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

def numericRow2159 : Integer.Sparse Master := [(Sum.inr 2143, 1), (Sum.inr 2176, 1), (Sum.inr 2185, 1), (Sum.inr 2212, 2), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

theorem reindexCheck2159 : Integer.Sparse.reindex keyMap MixedData.row2159 = numericRow2159 := by decide +kernel

theorem numericCheck2159 (x : Master → ℝ) : Integer.Sparse.eval numericRow2159 x =
    (1 : ℝ) * reducedSource2159 x := by
  norm_num [numericRow2159, reducedSource2159, Integer.Sparse.eval, Sparse.eval, nodeValue2143, nodeValue2176, nodeValue2185, nodeValue2212, nodeValue3588, nodeValue4074]

end MUB6.Certificate.MixedSourceBridge

end OAI
