import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramRows.Block4
import OAI.Analysis.MutuallyUnbiased.GramRows.Block5
import OAI.Analysis.MutuallyUnbiased.GramRows.Block6
import OAI.Analysis.MutuallyUnbiased.GramRows.Block7
import OAI.Analysis.MutuallyUnbiased.GramRows.Block8
import OAI.Analysis.MutuallyUnbiased.GramRows.Block9
import OAI.Analysis.MutuallyUnbiased.GramRows.Block10

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row252, row253, row254, row255, row256, row257, row258, row259, row260, row261, row262, row263, row264, row265, row266, row267, row268, row269, row270, row271, row272, row273, row274, row275, row276, row277, row278, row279, row280, row281, row282, row283, row284, row285, row286, row287, row288, row289, row290, row291, row292, row293]

theorem entryCheck3_0 : entry3_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_0 k)) := by decide +kernel

theorem rowsSound3_0 (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval252 x
  · exact rowEval253 x
  · exact rowEval254 x
  · exact rowEval255 x
  · exact rowEval256 x
  · exact rowEval257 x
  · exact rowEval258 x
  · exact rowEval259 x
  · exact rowEval260 x
  · exact rowEval261 x
  · exact rowEval262 x
  · exact rowEval263 x
  · exact rowEval264 x
  · exact rowEval265 x
  · exact rowEval266 x
  · exact rowEval267 x
  · exact rowEval268 x
  · exact rowEval269 x
  · exact rowEval270 x
  · exact rowEval271 x
  · exact rowEval272 x
  · exact rowEval273 x
  · exact rowEval274 x
  · exact rowEval275 x
  · exact rowEval276 x
  · exact rowEval277 x
  · exact rowEval278 x
  · exact rowEval279 x
  · exact rowEval280 x
  · exact rowEval281 x
  · exact rowEval282 x
  · exact rowEval283 x
  · exact rowEval284 x
  · exact rowEval285 x
  · exact rowEval286 x
  · exact rowEval287 x
  · exact rowEval288 x
  · exact rowEval289 x
  · exact rowEval290 x
  · exact rowEval291 x
  · exact rowEval292 x
  · exact rowEval293 x

theorem entryEval3_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_0 (GramNormalization.eval B) = GramFunctions.Block0.form3.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck3_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form3 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_0]

def rows3_1 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row294, row295, row296, row297, row298, row299, row300, row301, row302, row303, row304, row305, row306, row307, row308, row309, row310, row311, row312, row313, row314, row315, row316, row317, row318, row319, row320, row321, row322, row323, row324, row325, row326, row327, row328, row329, row330, row331, row332, row333, row334, row335]

theorem entryCheck3_1 : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

theorem rowsSound3_1 (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval294 x
  · exact rowEval295 x
  · exact rowEval296 x
  · exact rowEval297 x
  · exact rowEval298 x
  · exact rowEval299 x
  · exact rowEval300 x
  · exact rowEval301 x
  · exact rowEval302 x
  · exact rowEval303 x
  · exact rowEval304 x
  · exact rowEval305 x
  · exact rowEval306 x
  · exact rowEval307 x
  · exact rowEval308 x
  · exact rowEval309 x
  · exact rowEval310 x
  · exact rowEval311 x
  · exact rowEval312 x
  · exact rowEval313 x
  · exact rowEval314 x
  · exact rowEval315 x
  · exact rowEval316 x
  · exact rowEval317 x
  · exact rowEval318 x
  · exact rowEval319 x
  · exact rowEval320 x
  · exact rowEval321 x
  · exact rowEval322 x
  · exact rowEval323 x
  · exact rowEval324 x
  · exact rowEval325 x
  · exact rowEval326 x
  · exact rowEval327 x
  · exact rowEval328 x
  · exact rowEval329 x
  · exact rowEval330 x
  · exact rowEval331 x
  · exact rowEval332 x
  · exact rowEval333 x
  · exact rowEval334 x
  · exact rowEval335 x

theorem entryEval3_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_1 (GramNormalization.eval B) = GramFunctions.Block0.form3.mixedGram GramFunctions.Block0.form1 B := by
  rw [entryCheck3_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form3 GramFunctions.Block0.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_1]

def rows3_2 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row336, row337, row338, row339, row340, row341, row342, row343, row344, row345, row346, row347, row348, row349, row350, row351, row352, row353, row354, row355, row356, row357, row358, row359, row360, row361, row362, row363, row364, row365, row366, row367, row368, row369, row370, row371, row372, row373, row374, row375, row376, row377]

theorem entryCheck3_2 : entry3_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_2 k)) := by decide +kernel

theorem rowsSound3_2 (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form2) x := by
  fin_cases k
  · exact rowEval336 x
  · exact rowEval337 x
  · exact rowEval338 x
  · exact rowEval339 x
  · exact rowEval340 x
  · exact rowEval341 x
  · exact rowEval342 x
  · exact rowEval343 x
  · exact rowEval344 x
  · exact rowEval345 x
  · exact rowEval346 x
  · exact rowEval347 x
  · exact rowEval348 x
  · exact rowEval349 x
  · exact rowEval350 x
  · exact rowEval351 x
  · exact rowEval352 x
  · exact rowEval353 x
  · exact rowEval354 x
  · exact rowEval355 x
  · exact rowEval356 x
  · exact rowEval357 x
  · exact rowEval358 x
  · exact rowEval359 x
  · exact rowEval360 x
  · exact rowEval361 x
  · exact rowEval362 x
  · exact rowEval363 x
  · exact rowEval364 x
  · exact rowEval365 x
  · exact rowEval366 x
  · exact rowEval367 x
  · exact rowEval368 x
  · exact rowEval369 x
  · exact rowEval370 x
  · exact rowEval371 x
  · exact rowEval372 x
  · exact rowEval373 x
  · exact rowEval374 x
  · exact rowEval375 x
  · exact rowEval376 x
  · exact rowEval377 x

theorem entryEval3_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_2 (GramNormalization.eval B) = GramFunctions.Block0.form3.mixedGram GramFunctions.Block0.form2 B := by
  rw [entryCheck3_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form3 GramFunctions.Block0.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_2]

def rows3_3 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row378, row379, row380, row381, row382, row383, row384, row385, row386, row387, row388, row389, row390, row391, row392, row393, row394, row395, row396, row397, row398, row399, row400, row401, row402, row403, row404, row405, row406, row407, row408, row409, row410, row411, row412, row413, row414, row415, row416, row417, row418, row419]

theorem entryCheck3_3 : entry3_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_3 k)) := by decide +kernel

theorem rowsSound3_3 (k : Fin GramFunctions.Block0.form3.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows3_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form3.terms k).tag (GramFunctions.Block0.form3.terms k).charge GramFunctions.Block0.form3) x := by
  fin_cases k
  · exact rowEval378 x
  · exact rowEval379 x
  · exact rowEval380 x
  · exact rowEval381 x
  · exact rowEval382 x
  · exact rowEval383 x
  · exact rowEval384 x
  · exact rowEval385 x
  · exact rowEval386 x
  · exact rowEval387 x
  · exact rowEval388 x
  · exact rowEval389 x
  · exact rowEval390 x
  · exact rowEval391 x
  · exact rowEval392 x
  · exact rowEval393 x
  · exact rowEval394 x
  · exact rowEval395 x
  · exact rowEval396 x
  · exact rowEval397 x
  · exact rowEval398 x
  · exact rowEval399 x
  · exact rowEval400 x
  · exact rowEval401 x
  · exact rowEval402 x
  · exact rowEval403 x
  · exact rowEval404 x
  · exact rowEval405 x
  · exact rowEval406 x
  · exact rowEval407 x
  · exact rowEval408 x
  · exact rowEval409 x
  · exact rowEval410 x
  · exact rowEval411 x
  · exact rowEval412 x
  · exact rowEval413 x
  · exact rowEval414 x
  · exact rowEval415 x
  · exact rowEval416 x
  · exact rowEval417 x
  · exact rowEval418 x
  · exact rowEval419 x

theorem entryEval3_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry3_3 (GramNormalization.eval B) = GramFunctions.Block0.form3.mixedGram GramFunctions.Block0.form3 B := by
  rw [entryCheck3_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form3 GramFunctions.Block0.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound3_3]

end MUB6.Certificate.GramEntries.Block0

end OAI
