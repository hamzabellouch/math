import OAI.Analysis.MutuallyUnbiased.GramEntries.Block0Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramRows.Block10
import OAI.Analysis.MutuallyUnbiased.GramRows.Block11
import OAI.Analysis.MutuallyUnbiased.GramRows.Block12
import OAI.Analysis.MutuallyUnbiased.GramRows.Block13
import OAI.Analysis.MutuallyUnbiased.GramRows.Block14
import OAI.Analysis.MutuallyUnbiased.GramRows.Block15
import OAI.Analysis.MutuallyUnbiased.GramRows.Block16

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row420, row421, row422, row423, row424, row425, row426, row427, row428, row429, row430, row431, row432, row433, row434, row435, row436, row437, row438, row439, row440, row441, row442, row443, row444, row445, row446, row447, row448, row449, row450, row451, row452, row453, row454, row455, row456, row457, row458, row459, row460, row461]

theorem entryCheck4_0 : entry4_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form4.terms k).coefficient) (rows4_0 k)) := by decide +kernel

theorem rowsSound4_0 (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form0) x := by
  fin_cases k
  · exact rowEval420 x
  · exact rowEval421 x
  · exact rowEval422 x
  · exact rowEval423 x
  · exact rowEval424 x
  · exact rowEval425 x
  · exact rowEval426 x
  · exact rowEval427 x
  · exact rowEval428 x
  · exact rowEval429 x
  · exact rowEval430 x
  · exact rowEval431 x
  · exact rowEval432 x
  · exact rowEval433 x
  · exact rowEval434 x
  · exact rowEval435 x
  · exact rowEval436 x
  · exact rowEval437 x
  · exact rowEval438 x
  · exact rowEval439 x
  · exact rowEval440 x
  · exact rowEval441 x
  · exact rowEval442 x
  · exact rowEval443 x
  · exact rowEval444 x
  · exact rowEval445 x
  · exact rowEval446 x
  · exact rowEval447 x
  · exact rowEval448 x
  · exact rowEval449 x
  · exact rowEval450 x
  · exact rowEval451 x
  · exact rowEval452 x
  · exact rowEval453 x
  · exact rowEval454 x
  · exact rowEval455 x
  · exact rowEval456 x
  · exact rowEval457 x
  · exact rowEval458 x
  · exact rowEval459 x
  · exact rowEval460 x
  · exact rowEval461 x

theorem entryEval4_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_0 (GramNormalization.eval B) = GramFunctions.Block0.form4.mixedGram GramFunctions.Block0.form0 B := by
  rw [entryCheck4_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form4 GramFunctions.Block0.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_0]

def rows4_1 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row462, row463, row464, row465, row466, row467, row468, row469, row470, row471, row472, row473, row474, row475, row476, row477, row478, row479, row480, row481, row482, row483, row484, row485, row486, row487, row488, row489, row490, row491, row492, row493, row494, row495, row496, row497, row498, row499, row500, row501, row502, row503]

theorem entryCheck4_1 : entry4_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form4.terms k).coefficient) (rows4_1 k)) := by decide +kernel

theorem rowsSound4_1 (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form1) x := by
  fin_cases k
  · exact rowEval462 x
  · exact rowEval463 x
  · exact rowEval464 x
  · exact rowEval465 x
  · exact rowEval466 x
  · exact rowEval467 x
  · exact rowEval468 x
  · exact rowEval469 x
  · exact rowEval470 x
  · exact rowEval471 x
  · exact rowEval472 x
  · exact rowEval473 x
  · exact rowEval474 x
  · exact rowEval475 x
  · exact rowEval476 x
  · exact rowEval477 x
  · exact rowEval478 x
  · exact rowEval479 x
  · exact rowEval480 x
  · exact rowEval481 x
  · exact rowEval482 x
  · exact rowEval483 x
  · exact rowEval484 x
  · exact rowEval485 x
  · exact rowEval486 x
  · exact rowEval487 x
  · exact rowEval488 x
  · exact rowEval489 x
  · exact rowEval490 x
  · exact rowEval491 x
  · exact rowEval492 x
  · exact rowEval493 x
  · exact rowEval494 x
  · exact rowEval495 x
  · exact rowEval496 x
  · exact rowEval497 x
  · exact rowEval498 x
  · exact rowEval499 x
  · exact rowEval500 x
  · exact rowEval501 x
  · exact rowEval502 x
  · exact rowEval503 x

theorem entryEval4_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_1 (GramNormalization.eval B) = GramFunctions.Block0.form4.mixedGram GramFunctions.Block0.form1 B := by
  rw [entryCheck4_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form4 GramFunctions.Block0.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_1]

def rows4_2 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row504, row505, row506, row507, row508, row509, row510, row511, row512, row513, row514, row515, row516, row517, row518, row519, row520, row521, row522, row523, row524, row525, row526, row527, row528, row529, row530, row531, row532, row533, row534, row535, row536, row537, row538, row539, row540, row541, row542, row543, row544, row545]

theorem entryCheck4_2 : entry4_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form4.terms k).coefficient) (rows4_2 k)) := by decide +kernel

theorem rowsSound4_2 (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form2) x := by
  fin_cases k
  · exact rowEval504 x
  · exact rowEval505 x
  · exact rowEval506 x
  · exact rowEval507 x
  · exact rowEval508 x
  · exact rowEval509 x
  · exact rowEval510 x
  · exact rowEval511 x
  · exact rowEval512 x
  · exact rowEval513 x
  · exact rowEval514 x
  · exact rowEval515 x
  · exact rowEval516 x
  · exact rowEval517 x
  · exact rowEval518 x
  · exact rowEval519 x
  · exact rowEval520 x
  · exact rowEval521 x
  · exact rowEval522 x
  · exact rowEval523 x
  · exact rowEval524 x
  · exact rowEval525 x
  · exact rowEval526 x
  · exact rowEval527 x
  · exact rowEval528 x
  · exact rowEval529 x
  · exact rowEval530 x
  · exact rowEval531 x
  · exact rowEval532 x
  · exact rowEval533 x
  · exact rowEval534 x
  · exact rowEval535 x
  · exact rowEval536 x
  · exact rowEval537 x
  · exact rowEval538 x
  · exact rowEval539 x
  · exact rowEval540 x
  · exact rowEval541 x
  · exact rowEval542 x
  · exact rowEval543 x
  · exact rowEval544 x
  · exact rowEval545 x

theorem entryEval4_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_2 (GramNormalization.eval B) = GramFunctions.Block0.form4.mixedGram GramFunctions.Block0.form2 B := by
  rw [entryCheck4_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form4 GramFunctions.Block0.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_2]

def rows4_3 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row546, row547, row548, row549, row550, row551, row552, row553, row554, row555, row556, row557, row558, row559, row560, row561, row562, row563, row564, row565, row566, row567, row568, row569, row570, row571, row572, row573, row574, row575, row576, row577, row578, row579, row580, row581, row582, row583, row584, row585, row586, row587]

theorem entryCheck4_3 : entry4_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form4.terms k).coefficient) (rows4_3 k)) := by decide +kernel

theorem rowsSound4_3 (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form3) x := by
  fin_cases k
  · exact rowEval546 x
  · exact rowEval547 x
  · exact rowEval548 x
  · exact rowEval549 x
  · exact rowEval550 x
  · exact rowEval551 x
  · exact rowEval552 x
  · exact rowEval553 x
  · exact rowEval554 x
  · exact rowEval555 x
  · exact rowEval556 x
  · exact rowEval557 x
  · exact rowEval558 x
  · exact rowEval559 x
  · exact rowEval560 x
  · exact rowEval561 x
  · exact rowEval562 x
  · exact rowEval563 x
  · exact rowEval564 x
  · exact rowEval565 x
  · exact rowEval566 x
  · exact rowEval567 x
  · exact rowEval568 x
  · exact rowEval569 x
  · exact rowEval570 x
  · exact rowEval571 x
  · exact rowEval572 x
  · exact rowEval573 x
  · exact rowEval574 x
  · exact rowEval575 x
  · exact rowEval576 x
  · exact rowEval577 x
  · exact rowEval578 x
  · exact rowEval579 x
  · exact rowEval580 x
  · exact rowEval581 x
  · exact rowEval582 x
  · exact rowEval583 x
  · exact rowEval584 x
  · exact rowEval585 x
  · exact rowEval586 x
  · exact rowEval587 x

theorem entryEval4_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_3 (GramNormalization.eval B) = GramFunctions.Block0.form4.mixedGram GramFunctions.Block0.form3 B := by
  rw [entryCheck4_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form4 GramFunctions.Block0.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_3]

def rows4_4 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row588, row589, row590, row591, row592, row593, row594, row595, row596, row597, row598, row599, row600, row601, row602, row603, row604, row605, row606, row607, row608, row609, row610, row611, row612, row613, row614, row615, row616, row617, row618, row619, row620, row621, row622, row623, row624, row625, row626, row627, row628, row629]

theorem entryCheck4_4 : entry4_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form4.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form4.terms k).coefficient) (rows4_4 k)) := by decide +kernel

theorem rowsSound4_4 (k : Fin GramFunctions.Block0.form4.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows4_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block0.form4.terms k).tag (GramFunctions.Block0.form4.terms k).charge GramFunctions.Block0.form4) x := by
  fin_cases k
  · exact rowEval588 x
  · exact rowEval589 x
  · exact rowEval590 x
  · exact rowEval591 x
  · exact rowEval592 x
  · exact rowEval593 x
  · exact rowEval594 x
  · exact rowEval595 x
  · exact rowEval596 x
  · exact rowEval597 x
  · exact rowEval598 x
  · exact rowEval599 x
  · exact rowEval600 x
  · exact rowEval601 x
  · exact rowEval602 x
  · exact rowEval603 x
  · exact rowEval604 x
  · exact rowEval605 x
  · exact rowEval606 x
  · exact rowEval607 x
  · exact rowEval608 x
  · exact rowEval609 x
  · exact rowEval610 x
  · exact rowEval611 x
  · exact rowEval612 x
  · exact rowEval613 x
  · exact rowEval614 x
  · exact rowEval615 x
  · exact rowEval616 x
  · exact rowEval617 x
  · exact rowEval618 x
  · exact rowEval619 x
  · exact rowEval620 x
  · exact rowEval621 x
  · exact rowEval622 x
  · exact rowEval623 x
  · exact rowEval624 x
  · exact rowEval625 x
  · exact rowEval626 x
  · exact rowEval627 x
  · exact rowEval628 x
  · exact rowEval629 x

theorem entryEval4_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry4_4 (GramNormalization.eval B) = GramFunctions.Block0.form4.mixedGram GramFunctions.Block0.form4 B := by
  rw [entryCheck4_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block0.form4 GramFunctions.Block0.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound4_4]

end MUB6.Certificate.GramEntries.Block0

end OAI
