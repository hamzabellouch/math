import OAI.Analysis.MutuallyUnbiased.GramEntries.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block149
import OAI.Analysis.MutuallyUnbiased.GramRows.Block150
import OAI.Analysis.MutuallyUnbiased.GramRows.Block151
import OAI.Analysis.MutuallyUnbiased.GramRows.Block152
import OAI.Analysis.MutuallyUnbiased.GramRows.Block153
import OAI.Analysis.MutuallyUnbiased.GramRows.Block154

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16095, row16096, row16097, row16098, row16099, row16100, row16101, row16102, row16103, row16104, row16105, row16106, row16107, row16108, row16109, row16110, row16111, row16112, row16113, row16114, row16115, row16116, row16117, row16118, row16119, row16120, row16121, row16122, row16123, row16124, row16125, row16126, row16127, row16128, row16129, row16130]

theorem entryCheck16_0 : entry16_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_0 k)) := by decide +kernel

theorem rowsSound16_0 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form0) x := by
  fin_cases k
  · exact rowEval16095 x
  · exact rowEval16096 x
  · exact rowEval16097 x
  · exact rowEval16098 x
  · exact rowEval16099 x
  · exact rowEval16100 x
  · exact rowEval16101 x
  · exact rowEval16102 x
  · exact rowEval16103 x
  · exact rowEval16104 x
  · exact rowEval16105 x
  · exact rowEval16106 x
  · exact rowEval16107 x
  · exact rowEval16108 x
  · exact rowEval16109 x
  · exact rowEval16110 x
  · exact rowEval16111 x
  · exact rowEval16112 x
  · exact rowEval16113 x
  · exact rowEval16114 x
  · exact rowEval16115 x
  · exact rowEval16116 x
  · exact rowEval16117 x
  · exact rowEval16118 x
  · exact rowEval16119 x
  · exact rowEval16120 x
  · exact rowEval16121 x
  · exact rowEval16122 x
  · exact rowEval16123 x
  · exact rowEval16124 x
  · exact rowEval16125 x
  · exact rowEval16126 x
  · exact rowEval16127 x
  · exact rowEval16128 x
  · exact rowEval16129 x
  · exact rowEval16130 x

theorem entryEval16_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_0 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form0 B := by
  rw [entryCheck16_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_0]

def rows16_1 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16131, row16132, row16133, row16134, row16135, row16136, row16137, row16138, row16139, row16140, row16141, row16142, row16143, row16144, row16145, row16146, row16147, row16148, row16149, row16150, row16151, row16152, row16153, row16154, row16155, row16156, row16157, row16158, row16159, row16160, row16161, row16162, row16163, row16164, row16165, row16166]

theorem entryCheck16_1 : entry16_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_1 k)) := by decide +kernel

theorem rowsSound16_1 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form1) x := by
  fin_cases k
  · exact rowEval16131 x
  · exact rowEval16132 x
  · exact rowEval16133 x
  · exact rowEval16134 x
  · exact rowEval16135 x
  · exact rowEval16136 x
  · exact rowEval16137 x
  · exact rowEval16138 x
  · exact rowEval16139 x
  · exact rowEval16140 x
  · exact rowEval16141 x
  · exact rowEval16142 x
  · exact rowEval16143 x
  · exact rowEval16144 x
  · exact rowEval16145 x
  · exact rowEval16146 x
  · exact rowEval16147 x
  · exact rowEval16148 x
  · exact rowEval16149 x
  · exact rowEval16150 x
  · exact rowEval16151 x
  · exact rowEval16152 x
  · exact rowEval16153 x
  · exact rowEval16154 x
  · exact rowEval16155 x
  · exact rowEval16156 x
  · exact rowEval16157 x
  · exact rowEval16158 x
  · exact rowEval16159 x
  · exact rowEval16160 x
  · exact rowEval16161 x
  · exact rowEval16162 x
  · exact rowEval16163 x
  · exact rowEval16164 x
  · exact rowEval16165 x
  · exact rowEval16166 x

theorem entryEval16_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_1 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form1 B := by
  rw [entryCheck16_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_1]

def rows16_2 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16167, row16168, row16169, row16170, row16171, row16172, row16173, row16174, row16175, row16176, row16177, row16178, row16179, row16180, row16181, row16182, row16183, row16184, row16185, row16186, row16187, row16188, row16189, row16190, row16191, row16192, row16193, row16194, row16195, row16196, row16197, row16198, row16199, row16200, row16201, row16202]

theorem entryCheck16_2 : entry16_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_2 k)) := by decide +kernel

theorem rowsSound16_2 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form2) x := by
  fin_cases k
  · exact rowEval16167 x
  · exact rowEval16168 x
  · exact rowEval16169 x
  · exact rowEval16170 x
  · exact rowEval16171 x
  · exact rowEval16172 x
  · exact rowEval16173 x
  · exact rowEval16174 x
  · exact rowEval16175 x
  · exact rowEval16176 x
  · exact rowEval16177 x
  · exact rowEval16178 x
  · exact rowEval16179 x
  · exact rowEval16180 x
  · exact rowEval16181 x
  · exact rowEval16182 x
  · exact rowEval16183 x
  · exact rowEval16184 x
  · exact rowEval16185 x
  · exact rowEval16186 x
  · exact rowEval16187 x
  · exact rowEval16188 x
  · exact rowEval16189 x
  · exact rowEval16190 x
  · exact rowEval16191 x
  · exact rowEval16192 x
  · exact rowEval16193 x
  · exact rowEval16194 x
  · exact rowEval16195 x
  · exact rowEval16196 x
  · exact rowEval16197 x
  · exact rowEval16198 x
  · exact rowEval16199 x
  · exact rowEval16200 x
  · exact rowEval16201 x
  · exact rowEval16202 x

theorem entryEval16_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_2 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form2 B := by
  rw [entryCheck16_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_2]

def rows16_3 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16203, row16204, row16205, row16206, row16207, row16208, row16209, row16210, row16211, row16212, row16213, row16214, row16215, row16216, row16217, row16218, row16219, row16220, row16221, row16222, row16223, row16224, row16225, row16226, row16227, row16228, row16229, row16230, row16231, row16232, row16233, row16234, row16235, row16236, row16237, row16238]

theorem entryCheck16_3 : entry16_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_3 k)) := by decide +kernel

theorem rowsSound16_3 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form3) x := by
  fin_cases k
  · exact rowEval16203 x
  · exact rowEval16204 x
  · exact rowEval16205 x
  · exact rowEval16206 x
  · exact rowEval16207 x
  · exact rowEval16208 x
  · exact rowEval16209 x
  · exact rowEval16210 x
  · exact rowEval16211 x
  · exact rowEval16212 x
  · exact rowEval16213 x
  · exact rowEval16214 x
  · exact rowEval16215 x
  · exact rowEval16216 x
  · exact rowEval16217 x
  · exact rowEval16218 x
  · exact rowEval16219 x
  · exact rowEval16220 x
  · exact rowEval16221 x
  · exact rowEval16222 x
  · exact rowEval16223 x
  · exact rowEval16224 x
  · exact rowEval16225 x
  · exact rowEval16226 x
  · exact rowEval16227 x
  · exact rowEval16228 x
  · exact rowEval16229 x
  · exact rowEval16230 x
  · exact rowEval16231 x
  · exact rowEval16232 x
  · exact rowEval16233 x
  · exact rowEval16234 x
  · exact rowEval16235 x
  · exact rowEval16236 x
  · exact rowEval16237 x
  · exact rowEval16238 x

theorem entryEval16_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_3 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form3 B := by
  rw [entryCheck16_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_3]

def rows16_4 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16239, row16240, row16241, row16242, row16243, row16244, row16245, row16246, row16247, row16248, row16249, row16250, row16251, row16252, row16253, row16254, row16255, row16256, row16257, row16258, row16259, row16260, row16261, row16262, row16263, row16264, row16265, row16266, row16267, row16268, row16269, row16270, row16271, row16272, row16273, row16274]

theorem entryCheck16_4 : entry16_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_4 k)) := by decide +kernel

theorem rowsSound16_4 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form4) x := by
  fin_cases k
  · exact rowEval16239 x
  · exact rowEval16240 x
  · exact rowEval16241 x
  · exact rowEval16242 x
  · exact rowEval16243 x
  · exact rowEval16244 x
  · exact rowEval16245 x
  · exact rowEval16246 x
  · exact rowEval16247 x
  · exact rowEval16248 x
  · exact rowEval16249 x
  · exact rowEval16250 x
  · exact rowEval16251 x
  · exact rowEval16252 x
  · exact rowEval16253 x
  · exact rowEval16254 x
  · exact rowEval16255 x
  · exact rowEval16256 x
  · exact rowEval16257 x
  · exact rowEval16258 x
  · exact rowEval16259 x
  · exact rowEval16260 x
  · exact rowEval16261 x
  · exact rowEval16262 x
  · exact rowEval16263 x
  · exact rowEval16264 x
  · exact rowEval16265 x
  · exact rowEval16266 x
  · exact rowEval16267 x
  · exact rowEval16268 x
  · exact rowEval16269 x
  · exact rowEval16270 x
  · exact rowEval16271 x
  · exact rowEval16272 x
  · exact rowEval16273 x
  · exact rowEval16274 x

theorem entryEval16_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_4 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form4 B := by
  rw [entryCheck16_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_4]

def rows16_5 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16275, row16276, row16277, row16278, row16279, row16280, row16281, row16282, row16283, row16284, row16285, row16286, row16287, row16288, row16289, row16290, row16291, row16292, row16293, row16294, row16295, row16296, row16297, row16298, row16299, row16300, row16301, row16302, row16303, row16304, row16305, row16306, row16307, row16308, row16309, row16310]

theorem entryCheck16_5 : entry16_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_5 k)) := by decide +kernel

theorem rowsSound16_5 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form5) x := by
  fin_cases k
  · exact rowEval16275 x
  · exact rowEval16276 x
  · exact rowEval16277 x
  · exact rowEval16278 x
  · exact rowEval16279 x
  · exact rowEval16280 x
  · exact rowEval16281 x
  · exact rowEval16282 x
  · exact rowEval16283 x
  · exact rowEval16284 x
  · exact rowEval16285 x
  · exact rowEval16286 x
  · exact rowEval16287 x
  · exact rowEval16288 x
  · exact rowEval16289 x
  · exact rowEval16290 x
  · exact rowEval16291 x
  · exact rowEval16292 x
  · exact rowEval16293 x
  · exact rowEval16294 x
  · exact rowEval16295 x
  · exact rowEval16296 x
  · exact rowEval16297 x
  · exact rowEval16298 x
  · exact rowEval16299 x
  · exact rowEval16300 x
  · exact rowEval16301 x
  · exact rowEval16302 x
  · exact rowEval16303 x
  · exact rowEval16304 x
  · exact rowEval16305 x
  · exact rowEval16306 x
  · exact rowEval16307 x
  · exact rowEval16308 x
  · exact rowEval16309 x
  · exact rowEval16310 x

theorem entryEval16_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_5 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form5 B := by
  rw [entryCheck16_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_5]

def rows16_6 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16311, row16312, row16313, row16314, row16315, row16316, row16317, row16318, row16319, row16320, row16321, row16322, row16323, row16324, row16325, row16326, row16327, row16328, row16329, row16330, row16331, row16332, row16333, row16334, row16335, row16336, row16337, row16338, row16339, row16340, row16341, row16342, row16343, row16344, row16345, row16346]

theorem entryCheck16_6 : entry16_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_6 k)) := by decide +kernel

theorem rowsSound16_6 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form6) x := by
  fin_cases k
  · exact rowEval16311 x
  · exact rowEval16312 x
  · exact rowEval16313 x
  · exact rowEval16314 x
  · exact rowEval16315 x
  · exact rowEval16316 x
  · exact rowEval16317 x
  · exact rowEval16318 x
  · exact rowEval16319 x
  · exact rowEval16320 x
  · exact rowEval16321 x
  · exact rowEval16322 x
  · exact rowEval16323 x
  · exact rowEval16324 x
  · exact rowEval16325 x
  · exact rowEval16326 x
  · exact rowEval16327 x
  · exact rowEval16328 x
  · exact rowEval16329 x
  · exact rowEval16330 x
  · exact rowEval16331 x
  · exact rowEval16332 x
  · exact rowEval16333 x
  · exact rowEval16334 x
  · exact rowEval16335 x
  · exact rowEval16336 x
  · exact rowEval16337 x
  · exact rowEval16338 x
  · exact rowEval16339 x
  · exact rowEval16340 x
  · exact rowEval16341 x
  · exact rowEval16342 x
  · exact rowEval16343 x
  · exact rowEval16344 x
  · exact rowEval16345 x
  · exact rowEval16346 x

theorem entryEval16_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_6 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form6 B := by
  rw [entryCheck16_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_6]

def rows16_7 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16347, row16348, row16349, row16350, row16351, row16352, row16353, row16354, row16355, row16356, row16357, row16358, row16359, row16360, row16361, row16362, row16363, row16364, row16365, row16366, row16367, row16368, row16369, row16370, row16371, row16372, row16373, row16374, row16375, row16376, row16377, row16378, row16379, row16380, row16381, row16382]

theorem entryCheck16_7 : entry16_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_7 k)) := by decide +kernel

theorem rowsSound16_7 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form7) x := by
  fin_cases k
  · exact rowEval16347 x
  · exact rowEval16348 x
  · exact rowEval16349 x
  · exact rowEval16350 x
  · exact rowEval16351 x
  · exact rowEval16352 x
  · exact rowEval16353 x
  · exact rowEval16354 x
  · exact rowEval16355 x
  · exact rowEval16356 x
  · exact rowEval16357 x
  · exact rowEval16358 x
  · exact rowEval16359 x
  · exact rowEval16360 x
  · exact rowEval16361 x
  · exact rowEval16362 x
  · exact rowEval16363 x
  · exact rowEval16364 x
  · exact rowEval16365 x
  · exact rowEval16366 x
  · exact rowEval16367 x
  · exact rowEval16368 x
  · exact rowEval16369 x
  · exact rowEval16370 x
  · exact rowEval16371 x
  · exact rowEval16372 x
  · exact rowEval16373 x
  · exact rowEval16374 x
  · exact rowEval16375 x
  · exact rowEval16376 x
  · exact rowEval16377 x
  · exact rowEval16378 x
  · exact rowEval16379 x
  · exact rowEval16380 x
  · exact rowEval16381 x
  · exact rowEval16382 x

theorem entryEval16_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_7 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form7 B := by
  rw [entryCheck16_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_7]

def rows16_8 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16383, row16384, row16385, row16386, row16387, row16388, row16389, row16390, row16391, row16392, row16393, row16394, row16395, row16396, row16397, row16398, row16399, row16400, row16401, row16402, row16403, row16404, row16405, row16406, row16407, row16408, row16409, row16410, row16411, row16412, row16413, row16414, row16415, row16416, row16417, row16418]

theorem entryCheck16_8 : entry16_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_8 k)) := by decide +kernel

theorem rowsSound16_8 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form8) x := by
  fin_cases k
  · exact rowEval16383 x
  · exact rowEval16384 x
  · exact rowEval16385 x
  · exact rowEval16386 x
  · exact rowEval16387 x
  · exact rowEval16388 x
  · exact rowEval16389 x
  · exact rowEval16390 x
  · exact rowEval16391 x
  · exact rowEval16392 x
  · exact rowEval16393 x
  · exact rowEval16394 x
  · exact rowEval16395 x
  · exact rowEval16396 x
  · exact rowEval16397 x
  · exact rowEval16398 x
  · exact rowEval16399 x
  · exact rowEval16400 x
  · exact rowEval16401 x
  · exact rowEval16402 x
  · exact rowEval16403 x
  · exact rowEval16404 x
  · exact rowEval16405 x
  · exact rowEval16406 x
  · exact rowEval16407 x
  · exact rowEval16408 x
  · exact rowEval16409 x
  · exact rowEval16410 x
  · exact rowEval16411 x
  · exact rowEval16412 x
  · exact rowEval16413 x
  · exact rowEval16414 x
  · exact rowEval16415 x
  · exact rowEval16416 x
  · exact rowEval16417 x
  · exact rowEval16418 x

theorem entryEval16_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_8 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form8 B := by
  rw [entryCheck16_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_8]

def rows16_9 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16419, row16420, row16421, row16422, row16423, row16424, row16425, row16426, row16427, row16428, row16429, row16430, row16431, row16432, row16433, row16434, row16435, row16436, row16437, row16438, row16439, row16440, row16441, row16442, row16443, row16444, row16445, row16446, row16447, row16448, row16449, row16450, row16451, row16452, row16453, row16454]

theorem entryCheck16_9 : entry16_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_9 k)) := by decide +kernel

theorem rowsSound16_9 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form9) x := by
  fin_cases k
  · exact rowEval16419 x
  · exact rowEval16420 x
  · exact rowEval16421 x
  · exact rowEval16422 x
  · exact rowEval16423 x
  · exact rowEval16424 x
  · exact rowEval16425 x
  · exact rowEval16426 x
  · exact rowEval16427 x
  · exact rowEval16428 x
  · exact rowEval16429 x
  · exact rowEval16430 x
  · exact rowEval16431 x
  · exact rowEval16432 x
  · exact rowEval16433 x
  · exact rowEval16434 x
  · exact rowEval16435 x
  · exact rowEval16436 x
  · exact rowEval16437 x
  · exact rowEval16438 x
  · exact rowEval16439 x
  · exact rowEval16440 x
  · exact rowEval16441 x
  · exact rowEval16442 x
  · exact rowEval16443 x
  · exact rowEval16444 x
  · exact rowEval16445 x
  · exact rowEval16446 x
  · exact rowEval16447 x
  · exact rowEval16448 x
  · exact rowEval16449 x
  · exact rowEval16450 x
  · exact rowEval16451 x
  · exact rowEval16452 x
  · exact rowEval16453 x
  · exact rowEval16454 x

theorem entryEval16_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_9 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form9 B := by
  rw [entryCheck16_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_9]

def rows16_10 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16455, row16456, row16457, row16458, row16459, row16460, row16461, row16462, row16463, row16464, row16465, row16466, row16467, row16468, row16469, row16470, row16471, row16472, row16473, row16474, row16475, row16476, row16477, row16478, row16479, row16480, row16481, row16482, row16483, row16484, row16485, row16486, row16487, row16488, row16489, row16490]

theorem entryCheck16_10 : entry16_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_10 k)) := by decide +kernel

theorem rowsSound16_10 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form10) x := by
  fin_cases k
  · exact rowEval16455 x
  · exact rowEval16456 x
  · exact rowEval16457 x
  · exact rowEval16458 x
  · exact rowEval16459 x
  · exact rowEval16460 x
  · exact rowEval16461 x
  · exact rowEval16462 x
  · exact rowEval16463 x
  · exact rowEval16464 x
  · exact rowEval16465 x
  · exact rowEval16466 x
  · exact rowEval16467 x
  · exact rowEval16468 x
  · exact rowEval16469 x
  · exact rowEval16470 x
  · exact rowEval16471 x
  · exact rowEval16472 x
  · exact rowEval16473 x
  · exact rowEval16474 x
  · exact rowEval16475 x
  · exact rowEval16476 x
  · exact rowEval16477 x
  · exact rowEval16478 x
  · exact rowEval16479 x
  · exact rowEval16480 x
  · exact rowEval16481 x
  · exact rowEval16482 x
  · exact rowEval16483 x
  · exact rowEval16484 x
  · exact rowEval16485 x
  · exact rowEval16486 x
  · exact rowEval16487 x
  · exact rowEval16488 x
  · exact rowEval16489 x
  · exact rowEval16490 x

theorem entryEval16_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_10 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form10 B := by
  rw [entryCheck16_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_10]

def rows16_11 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16491, row16492, row16493, row16494, row16495, row16496, row16497, row16498, row16499, row16500, row16501, row16502, row16503, row16504, row16505, row16506, row16507, row16508, row16509, row16510, row16511, row16512, row16513, row16514, row16515, row16516, row16517, row16518, row16519, row16520, row16521, row16522, row16523, row16524, row16525, row16526]

theorem entryCheck16_11 : entry16_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_11 k)) := by decide +kernel

theorem rowsSound16_11 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form11) x := by
  fin_cases k
  · exact rowEval16491 x
  · exact rowEval16492 x
  · exact rowEval16493 x
  · exact rowEval16494 x
  · exact rowEval16495 x
  · exact rowEval16496 x
  · exact rowEval16497 x
  · exact rowEval16498 x
  · exact rowEval16499 x
  · exact rowEval16500 x
  · exact rowEval16501 x
  · exact rowEval16502 x
  · exact rowEval16503 x
  · exact rowEval16504 x
  · exact rowEval16505 x
  · exact rowEval16506 x
  · exact rowEval16507 x
  · exact rowEval16508 x
  · exact rowEval16509 x
  · exact rowEval16510 x
  · exact rowEval16511 x
  · exact rowEval16512 x
  · exact rowEval16513 x
  · exact rowEval16514 x
  · exact rowEval16515 x
  · exact rowEval16516 x
  · exact rowEval16517 x
  · exact rowEval16518 x
  · exact rowEval16519 x
  · exact rowEval16520 x
  · exact rowEval16521 x
  · exact rowEval16522 x
  · exact rowEval16523 x
  · exact rowEval16524 x
  · exact rowEval16525 x
  · exact rowEval16526 x

theorem entryEval16_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_11 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form11 B := by
  rw [entryCheck16_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_11]

def rows16_12 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16527, row16528, row16529, row16530, row16531, row16532, row16533, row16534, row16535, row16536, row16537, row16538, row16539, row16540, row16541, row16542, row16543, row16544, row16545, row16546, row16547, row16548, row16549, row16550, row16551, row16552, row16553, row16554, row16555, row16556, row16557, row16558, row16559, row16560, row16561, row16562]

theorem entryCheck16_12 : entry16_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_12 k)) := by decide +kernel

theorem rowsSound16_12 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form12) x := by
  fin_cases k
  · exact rowEval16527 x
  · exact rowEval16528 x
  · exact rowEval16529 x
  · exact rowEval16530 x
  · exact rowEval16531 x
  · exact rowEval16532 x
  · exact rowEval16533 x
  · exact rowEval16534 x
  · exact rowEval16535 x
  · exact rowEval16536 x
  · exact rowEval16537 x
  · exact rowEval16538 x
  · exact rowEval16539 x
  · exact rowEval16540 x
  · exact rowEval16541 x
  · exact rowEval16542 x
  · exact rowEval16543 x
  · exact rowEval16544 x
  · exact rowEval16545 x
  · exact rowEval16546 x
  · exact rowEval16547 x
  · exact rowEval16548 x
  · exact rowEval16549 x
  · exact rowEval16550 x
  · exact rowEval16551 x
  · exact rowEval16552 x
  · exact rowEval16553 x
  · exact rowEval16554 x
  · exact rowEval16555 x
  · exact rowEval16556 x
  · exact rowEval16557 x
  · exact rowEval16558 x
  · exact rowEval16559 x
  · exact rowEval16560 x
  · exact rowEval16561 x
  · exact rowEval16562 x

theorem entryEval16_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_12 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form12 B := by
  rw [entryCheck16_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_12]

def rows16_13 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16563, row16564, row16565, row16566, row16567, row16568, row16569, row16570, row16571, row16572, row16573, row16574, row16575, row16576, row16577, row16578, row16579, row16580, row16581, row16582, row16583, row16584, row16585, row16586, row16587, row16588, row16589, row16590, row16591, row16592, row16593, row16594, row16595, row16596, row16597, row16598]

theorem entryCheck16_13 : entry16_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_13 k)) := by decide +kernel

theorem rowsSound16_13 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form13) x := by
  fin_cases k
  · exact rowEval16563 x
  · exact rowEval16564 x
  · exact rowEval16565 x
  · exact rowEval16566 x
  · exact rowEval16567 x
  · exact rowEval16568 x
  · exact rowEval16569 x
  · exact rowEval16570 x
  · exact rowEval16571 x
  · exact rowEval16572 x
  · exact rowEval16573 x
  · exact rowEval16574 x
  · exact rowEval16575 x
  · exact rowEval16576 x
  · exact rowEval16577 x
  · exact rowEval16578 x
  · exact rowEval16579 x
  · exact rowEval16580 x
  · exact rowEval16581 x
  · exact rowEval16582 x
  · exact rowEval16583 x
  · exact rowEval16584 x
  · exact rowEval16585 x
  · exact rowEval16586 x
  · exact rowEval16587 x
  · exact rowEval16588 x
  · exact rowEval16589 x
  · exact rowEval16590 x
  · exact rowEval16591 x
  · exact rowEval16592 x
  · exact rowEval16593 x
  · exact rowEval16594 x
  · exact rowEval16595 x
  · exact rowEval16596 x
  · exact rowEval16597 x
  · exact rowEval16598 x

theorem entryEval16_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_13 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form13 B := by
  rw [entryCheck16_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_13]

def rows16_14 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16599, row16600, row16601, row16602, row16603, row16604, row16605, row16606, row16607, row16608, row16609, row16610, row16611, row16612, row16613, row16614, row16615, row16616, row16617, row16618, row16619, row16620, row16621, row16622, row16623, row16624, row16625, row16626, row16627, row16628, row16629, row16630, row16631, row16632, row16633, row16634]

theorem entryCheck16_14 : entry16_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_14 k)) := by decide +kernel

theorem rowsSound16_14 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form14) x := by
  fin_cases k
  · exact rowEval16599 x
  · exact rowEval16600 x
  · exact rowEval16601 x
  · exact rowEval16602 x
  · exact rowEval16603 x
  · exact rowEval16604 x
  · exact rowEval16605 x
  · exact rowEval16606 x
  · exact rowEval16607 x
  · exact rowEval16608 x
  · exact rowEval16609 x
  · exact rowEval16610 x
  · exact rowEval16611 x
  · exact rowEval16612 x
  · exact rowEval16613 x
  · exact rowEval16614 x
  · exact rowEval16615 x
  · exact rowEval16616 x
  · exact rowEval16617 x
  · exact rowEval16618 x
  · exact rowEval16619 x
  · exact rowEval16620 x
  · exact rowEval16621 x
  · exact rowEval16622 x
  · exact rowEval16623 x
  · exact rowEval16624 x
  · exact rowEval16625 x
  · exact rowEval16626 x
  · exact rowEval16627 x
  · exact rowEval16628 x
  · exact rowEval16629 x
  · exact rowEval16630 x
  · exact rowEval16631 x
  · exact rowEval16632 x
  · exact rowEval16633 x
  · exact rowEval16634 x

theorem entryEval16_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_14 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form14 B := by
  rw [entryCheck16_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_14]

def rows16_15 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16635, row16636, row16637, row16638, row16639, row16640, row16641, row16642, row16643, row16644, row16645, row16646, row16647, row16648, row16649, row16650, row16651, row16652, row16653, row16654, row16655, row16656, row16657, row16658, row16659, row16660, row16661, row16662, row16663, row16664, row16665, row16666, row16667, row16668, row16669, row16670]

theorem entryCheck16_15 : entry16_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_15 k)) := by decide +kernel

theorem rowsSound16_15 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form15) x := by
  fin_cases k
  · exact rowEval16635 x
  · exact rowEval16636 x
  · exact rowEval16637 x
  · exact rowEval16638 x
  · exact rowEval16639 x
  · exact rowEval16640 x
  · exact rowEval16641 x
  · exact rowEval16642 x
  · exact rowEval16643 x
  · exact rowEval16644 x
  · exact rowEval16645 x
  · exact rowEval16646 x
  · exact rowEval16647 x
  · exact rowEval16648 x
  · exact rowEval16649 x
  · exact rowEval16650 x
  · exact rowEval16651 x
  · exact rowEval16652 x
  · exact rowEval16653 x
  · exact rowEval16654 x
  · exact rowEval16655 x
  · exact rowEval16656 x
  · exact rowEval16657 x
  · exact rowEval16658 x
  · exact rowEval16659 x
  · exact rowEval16660 x
  · exact rowEval16661 x
  · exact rowEval16662 x
  · exact rowEval16663 x
  · exact rowEval16664 x
  · exact rowEval16665 x
  · exact rowEval16666 x
  · exact rowEval16667 x
  · exact rowEval16668 x
  · exact rowEval16669 x
  · exact rowEval16670 x

theorem entryEval16_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_15 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form15 B := by
  rw [entryCheck16_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_15]

def rows16_16 : Fin GramFunctions.Block4.form16.size → Integer.Sparse Key := ![row16671, row16672, row16673, row16674, row16675, row16676, row16677, row16678, row16679, row16680, row16681, row16682, row16683, row16684, row16685, row16686, row16687, row16688, row16689, row16690, row16691, row16692, row16693, row16694, row16695, row16696, row16697, row16698, row16699, row16700, row16701, row16702, row16703, row16704, row16705, row16706]

theorem entryCheck16_16 : entry16_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block4.form16.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block4.form16.terms k).coefficient) (rows16_16 k)) := by decide +kernel

theorem rowsSound16_16 (k : Fin GramFunctions.Block4.form16.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows16_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block4.form16.terms k).tag (GramFunctions.Block4.form16.terms k).charge GramFunctions.Block4.form16) x := by
  fin_cases k
  · exact rowEval16671 x
  · exact rowEval16672 x
  · exact rowEval16673 x
  · exact rowEval16674 x
  · exact rowEval16675 x
  · exact rowEval16676 x
  · exact rowEval16677 x
  · exact rowEval16678 x
  · exact rowEval16679 x
  · exact rowEval16680 x
  · exact rowEval16681 x
  · exact rowEval16682 x
  · exact rowEval16683 x
  · exact rowEval16684 x
  · exact rowEval16685 x
  · exact rowEval16686 x
  · exact rowEval16687 x
  · exact rowEval16688 x
  · exact rowEval16689 x
  · exact rowEval16690 x
  · exact rowEval16691 x
  · exact rowEval16692 x
  · exact rowEval16693 x
  · exact rowEval16694 x
  · exact rowEval16695 x
  · exact rowEval16696 x
  · exact rowEval16697 x
  · exact rowEval16698 x
  · exact rowEval16699 x
  · exact rowEval16700 x
  · exact rowEval16701 x
  · exact rowEval16702 x
  · exact rowEval16703 x
  · exact rowEval16704 x
  · exact rowEval16705 x
  · exact rowEval16706 x

theorem entryEval16_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry16_16 (GramNormalization.eval B) = GramFunctions.Block4.form16.mixedGram GramFunctions.Block4.form16 B := by
  rw [entryCheck16_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block4.form16 GramFunctions.Block4.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound16_16]

end MUB6.Certificate.GramEntries.Block4

end OAI
