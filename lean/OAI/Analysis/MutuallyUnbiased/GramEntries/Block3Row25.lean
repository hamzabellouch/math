import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block120
import OAI.Analysis.MutuallyUnbiased.GramRows.Block121

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows25_0 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12331, row12332, row12333, row12334, row12335, row12336, row12337, row12338]

theorem entryCheck25_0 : entry25_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_0 k)) := by decide +kernel

theorem rowsSound25_0 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval12331 x
  · exact rowEval12332 x
  · exact rowEval12333 x
  · exact rowEval12334 x
  · exact rowEval12335 x
  · exact rowEval12336 x
  · exact rowEval12337 x
  · exact rowEval12338 x

theorem entryEval25_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_0 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck25_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_0]

def rows25_1 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12339, row12340, row12341, row12342, row12343, row12344, row12345, row12346]

theorem entryCheck25_1 : entry25_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_1 k)) := by decide +kernel

theorem rowsSound25_1 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12339 x
  · exact rowEval12340 x
  · exact rowEval12341 x
  · exact rowEval12342 x
  · exact rowEval12343 x
  · exact rowEval12344 x
  · exact rowEval12345 x
  · exact rowEval12346 x

theorem entryEval25_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_1 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck25_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_1]

def rows25_2 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12347, row12348, row12349, row12350, row12351, row12352, row12353, row12354]

theorem entryCheck25_2 : entry25_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_2 k)) := by decide +kernel

theorem rowsSound25_2 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12347 x
  · exact rowEval12348 x
  · exact rowEval12349 x
  · exact rowEval12350 x
  · exact rowEval12351 x
  · exact rowEval12352 x
  · exact rowEval12353 x
  · exact rowEval12354 x

theorem entryEval25_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_2 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck25_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_2]

def rows25_3 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12355, row12356, row12357, row12358, row12359, row12360, row12361, row12362]

theorem entryCheck25_3 : entry25_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_3 k)) := by decide +kernel

theorem rowsSound25_3 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12355 x
  · exact rowEval12356 x
  · exact rowEval12357 x
  · exact rowEval12358 x
  · exact rowEval12359 x
  · exact rowEval12360 x
  · exact rowEval12361 x
  · exact rowEval12362 x

theorem entryEval25_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_3 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck25_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_3]

def rows25_4 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12363, row12364, row12365, row12366, row12367, row12368, row12369, row12370]

theorem entryCheck25_4 : entry25_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_4 k)) := by decide +kernel

theorem rowsSound25_4 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12363 x
  · exact rowEval12364 x
  · exact rowEval12365 x
  · exact rowEval12366 x
  · exact rowEval12367 x
  · exact rowEval12368 x
  · exact rowEval12369 x
  · exact rowEval12370 x

theorem entryEval25_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_4 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck25_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_4]

def rows25_5 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12371, row12372, row12373, row12374, row12375, row12376, row12377, row12378]

theorem entryCheck25_5 : entry25_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_5 k)) := by decide +kernel

theorem rowsSound25_5 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval12371 x
  · exact rowEval12372 x
  · exact rowEval12373 x
  · exact rowEval12374 x
  · exact rowEval12375 x
  · exact rowEval12376 x
  · exact rowEval12377 x
  · exact rowEval12378 x

theorem entryEval25_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_5 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck25_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_5]

def rows25_6 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12379, row12380, row12381, row12382, row12383, row12384, row12385, row12386]

theorem entryCheck25_6 : entry25_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_6 k)) := by decide +kernel

theorem rowsSound25_6 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12379 x
  · exact rowEval12380 x
  · exact rowEval12381 x
  · exact rowEval12382 x
  · exact rowEval12383 x
  · exact rowEval12384 x
  · exact rowEval12385 x
  · exact rowEval12386 x

theorem entryEval25_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_6 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck25_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_6]

def rows25_7 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12387, row12388, row12389, row12390, row12391, row12392, row12393, row12394]

theorem entryCheck25_7 : entry25_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_7 k)) := by decide +kernel

theorem rowsSound25_7 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval12387 x
  · exact rowEval12388 x
  · exact rowEval12389 x
  · exact rowEval12390 x
  · exact rowEval12391 x
  · exact rowEval12392 x
  · exact rowEval12393 x
  · exact rowEval12394 x

theorem entryEval25_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_7 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck25_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_7]

def rows25_8 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12395, row12396, row12397, row12398, row12399, row12400, row12401, row12402]

theorem entryCheck25_8 : entry25_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_8 k)) := by decide +kernel

theorem rowsSound25_8 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval12395 x
  · exact rowEval12396 x
  · exact rowEval12397 x
  · exact rowEval12398 x
  · exact rowEval12399 x
  · exact rowEval12400 x
  · exact rowEval12401 x
  · exact rowEval12402 x

theorem entryEval25_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_8 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck25_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_8]

def rows25_9 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12403, row12404, row12405, row12406, row12407, row12408, row12409, row12410]

theorem entryCheck25_9 : entry25_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_9 k)) := by decide +kernel

theorem rowsSound25_9 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval12403 x
  · exact rowEval12404 x
  · exact rowEval12405 x
  · exact rowEval12406 x
  · exact rowEval12407 x
  · exact rowEval12408 x
  · exact rowEval12409 x
  · exact rowEval12410 x

theorem entryEval25_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_9 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck25_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_9]

def rows25_10 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12411, row12412, row12413, row12414, row12415, row12416, row12417, row12418]

theorem entryCheck25_10 : entry25_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_10 k)) := by decide +kernel

theorem rowsSound25_10 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval12411 x
  · exact rowEval12412 x
  · exact rowEval12413 x
  · exact rowEval12414 x
  · exact rowEval12415 x
  · exact rowEval12416 x
  · exact rowEval12417 x
  · exact rowEval12418 x

theorem entryEval25_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_10 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck25_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_10]

def rows25_11 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12419, row12420, row12421, row12422, row12423, row12424, row12425, row12426]

theorem entryCheck25_11 : entry25_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_11 k)) := by decide +kernel

theorem rowsSound25_11 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12419 x
  · exact rowEval12420 x
  · exact rowEval12421 x
  · exact rowEval12422 x
  · exact rowEval12423 x
  · exact rowEval12424 x
  · exact rowEval12425 x
  · exact rowEval12426 x

theorem entryEval25_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_11 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck25_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_11]

def rows25_12 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12427, row12428, row12429, row12430, row12431, row12432, row12433, row12434]

theorem entryCheck25_12 : entry25_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_12 k)) := by decide +kernel

theorem rowsSound25_12 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval12427 x
  · exact rowEval12428 x
  · exact rowEval12429 x
  · exact rowEval12430 x
  · exact rowEval12431 x
  · exact rowEval12432 x
  · exact rowEval12433 x
  · exact rowEval12434 x

theorem entryEval25_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_12 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck25_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_12]

def rows25_13 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12435, row12436, row12437, row12438, row12439, row12440, row12441, row12442]

theorem entryCheck25_13 : entry25_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_13 k)) := by decide +kernel

theorem rowsSound25_13 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12435 x
  · exact rowEval12436 x
  · exact rowEval12437 x
  · exact rowEval12438 x
  · exact rowEval12439 x
  · exact rowEval12440 x
  · exact rowEval12441 x
  · exact rowEval12442 x

theorem entryEval25_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_13 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck25_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_13]

def rows25_14 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12443, row12444, row12445, row12446, row12447, row12448, row12449, row12450]

theorem entryCheck25_14 : entry25_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_14 k)) := by decide +kernel

theorem rowsSound25_14 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12443 x
  · exact rowEval12444 x
  · exact rowEval12445 x
  · exact rowEval12446 x
  · exact rowEval12447 x
  · exact rowEval12448 x
  · exact rowEval12449 x
  · exact rowEval12450 x

theorem entryEval25_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_14 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck25_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_14]

def rows25_15 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12451, row12452, row12453, row12454, row12455, row12456, row12457, row12458]

theorem entryCheck25_15 : entry25_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_15 k)) := by decide +kernel

theorem rowsSound25_15 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12451 x
  · exact rowEval12452 x
  · exact rowEval12453 x
  · exact rowEval12454 x
  · exact rowEval12455 x
  · exact rowEval12456 x
  · exact rowEval12457 x
  · exact rowEval12458 x

theorem entryEval25_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_15 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck25_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_15]

def rows25_16 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12459, row12460, row12461, row12462, row12463, row12464, row12465, row12466]

theorem entryCheck25_16 : entry25_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_16 k)) := by decide +kernel

theorem rowsSound25_16 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12459 x
  · exact rowEval12460 x
  · exact rowEval12461 x
  · exact rowEval12462 x
  · exact rowEval12463 x
  · exact rowEval12464 x
  · exact rowEval12465 x
  · exact rowEval12466 x

theorem entryEval25_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_16 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck25_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_16]

def rows25_17 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12467, row12468, row12469, row12470, row12471, row12472, row12473, row12474]

theorem entryCheck25_17 : entry25_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_17 k)) := by decide +kernel

theorem rowsSound25_17 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12467 x
  · exact rowEval12468 x
  · exact rowEval12469 x
  · exact rowEval12470 x
  · exact rowEval12471 x
  · exact rowEval12472 x
  · exact rowEval12473 x
  · exact rowEval12474 x

theorem entryEval25_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_17 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck25_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_17]

def rows25_18 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12475, row12476, row12477, row12478, row12479, row12480, row12481, row12482]

theorem entryCheck25_18 : entry25_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_18 k)) := by decide +kernel

theorem rowsSound25_18 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12475 x
  · exact rowEval12476 x
  · exact rowEval12477 x
  · exact rowEval12478 x
  · exact rowEval12479 x
  · exact rowEval12480 x
  · exact rowEval12481 x
  · exact rowEval12482 x

theorem entryEval25_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_18 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck25_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_18]

def rows25_19 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12483, row12484, row12485, row12486, row12487, row12488, row12489, row12490]

theorem entryCheck25_19 : entry25_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_19 k)) := by decide +kernel

theorem rowsSound25_19 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12483 x
  · exact rowEval12484 x
  · exact rowEval12485 x
  · exact rowEval12486 x
  · exact rowEval12487 x
  · exact rowEval12488 x
  · exact rowEval12489 x
  · exact rowEval12490 x

theorem entryEval25_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_19 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck25_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_19]

def rows25_20 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12491, row12492, row12493, row12494, row12495, row12496, row12497, row12498]

theorem entryCheck25_20 : entry25_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_20 k)) := by decide +kernel

theorem rowsSound25_20 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12491 x
  · exact rowEval12492 x
  · exact rowEval12493 x
  · exact rowEval12494 x
  · exact rowEval12495 x
  · exact rowEval12496 x
  · exact rowEval12497 x
  · exact rowEval12498 x

theorem entryEval25_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_20 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck25_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_20]

def rows25_21 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12499, row12500, row12501, row12502, row12503, row12504, row12505, row12506]

theorem entryCheck25_21 : entry25_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_21 k)) := by decide +kernel

theorem rowsSound25_21 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval12499 x
  · exact rowEval12500 x
  · exact rowEval12501 x
  · exact rowEval12502 x
  · exact rowEval12503 x
  · exact rowEval12504 x
  · exact rowEval12505 x
  · exact rowEval12506 x

theorem entryEval25_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_21 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck25_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_21]

def rows25_22 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12507, row12508, row12509, row12510, row12511, row12512, row12513, row12514]

theorem entryCheck25_22 : entry25_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_22 k)) := by decide +kernel

theorem rowsSound25_22 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval12507 x
  · exact rowEval12508 x
  · exact rowEval12509 x
  · exact rowEval12510 x
  · exact rowEval12511 x
  · exact rowEval12512 x
  · exact rowEval12513 x
  · exact rowEval12514 x

theorem entryEval25_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_22 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck25_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_22]

def rows25_23 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12515, row12516, row12517, row12518, row12519, row12520, row12521, row12522]

theorem entryCheck25_23 : entry25_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_23 k)) := by decide +kernel

theorem rowsSound25_23 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12515 x
  · exact rowEval12516 x
  · exact rowEval12517 x
  · exact rowEval12518 x
  · exact rowEval12519 x
  · exact rowEval12520 x
  · exact rowEval12521 x
  · exact rowEval12522 x

theorem entryEval25_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_23 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck25_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_23]

def rows25_24 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12523, row12524, row12525, row12526, row12527, row12528, row12529, row12530]

theorem entryCheck25_24 : entry25_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_24 k)) := by decide +kernel

theorem rowsSound25_24 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval12523 x
  · exact rowEval12524 x
  · exact rowEval12525 x
  · exact rowEval12526 x
  · exact rowEval12527 x
  · exact rowEval12528 x
  · exact rowEval12529 x
  · exact rowEval12530 x

theorem entryEval25_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_24 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck25_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_24]

def rows25_25 : Fin GramFunctions.Block3.form25.size → Integer.Sparse Key := ![row12531, row12532, row12533, row12534, row12535, row12536, row12537, row12538]

theorem entryCheck25_25 : entry25_25 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_25 k)) := by decide +kernel

theorem rowsSound25_25 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_25 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form25) x := by
  fin_cases k
  · exact rowEval12531 x
  · exact rowEval12532 x
  · exact rowEval12533 x
  · exact rowEval12534 x
  · exact rowEval12535 x
  · exact rowEval12536 x
  · exact rowEval12537 x
  · exact rowEval12538 x

theorem entryEval25_25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_25 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form25 B := by
  rw [entryCheck25_25, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form25 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_25]

end MUB6.Certificate.GramEntries.Block3

end OAI
