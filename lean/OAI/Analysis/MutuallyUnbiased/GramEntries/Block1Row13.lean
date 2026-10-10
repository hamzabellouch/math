import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block43
import OAI.Analysis.MutuallyUnbiased.GramRows.Block44

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2476, row2477, row2478, row2479, row2480, row2481, row2482, row2483, row2484, row2485, row2486, row2487, row2488, row2489]

theorem entryCheck13_0 : entry13_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_0 k)) := by decide +kernel

theorem rowsSound13_0 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval2476 x
  · exact rowEval2477 x
  · exact rowEval2478 x
  · exact rowEval2479 x
  · exact rowEval2480 x
  · exact rowEval2481 x
  · exact rowEval2482 x
  · exact rowEval2483 x
  · exact rowEval2484 x
  · exact rowEval2485 x
  · exact rowEval2486 x
  · exact rowEval2487 x
  · exact rowEval2488 x
  · exact rowEval2489 x

theorem entryEval13_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_0 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck13_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_0]

def rows13_1 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2490, row2491, row2492, row2493, row2494, row2495, row2496, row2497, row2498, row2499, row2500, row2501, row2502, row2503]

theorem entryCheck13_1 : entry13_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_1 k)) := by decide +kernel

theorem rowsSound13_1 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2490 x
  · exact rowEval2491 x
  · exact rowEval2492 x
  · exact rowEval2493 x
  · exact rowEval2494 x
  · exact rowEval2495 x
  · exact rowEval2496 x
  · exact rowEval2497 x
  · exact rowEval2498 x
  · exact rowEval2499 x
  · exact rowEval2500 x
  · exact rowEval2501 x
  · exact rowEval2502 x
  · exact rowEval2503 x

theorem entryEval13_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_1 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck13_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_1]

def rows13_2 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2504, row2505, row2506, row2507, row2508, row2509, row2510, row2511, row2512, row2513, row2514, row2515, row2516, row2517]

theorem entryCheck13_2 : entry13_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_2 k)) := by decide +kernel

theorem rowsSound13_2 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval2504 x
  · exact rowEval2505 x
  · exact rowEval2506 x
  · exact rowEval2507 x
  · exact rowEval2508 x
  · exact rowEval2509 x
  · exact rowEval2510 x
  · exact rowEval2511 x
  · exact rowEval2512 x
  · exact rowEval2513 x
  · exact rowEval2514 x
  · exact rowEval2515 x
  · exact rowEval2516 x
  · exact rowEval2517 x

theorem entryEval13_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_2 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck13_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_2]

def rows13_3 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2518, row2519, row2520, row2521, row2522, row2523, row2524, row2525, row2526, row2527, row2528, row2529, row2530, row2531]

theorem entryCheck13_3 : entry13_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_3 k)) := by decide +kernel

theorem rowsSound13_3 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2518 x
  · exact rowEval2519 x
  · exact rowEval2520 x
  · exact rowEval2521 x
  · exact rowEval2522 x
  · exact rowEval2523 x
  · exact rowEval2524 x
  · exact rowEval2525 x
  · exact rowEval2526 x
  · exact rowEval2527 x
  · exact rowEval2528 x
  · exact rowEval2529 x
  · exact rowEval2530 x
  · exact rowEval2531 x

theorem entryEval13_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_3 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck13_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_3]

def rows13_4 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2532, row2533, row2534, row2535, row2536, row2537, row2538, row2539, row2540, row2541, row2542, row2543, row2544, row2545]

theorem entryCheck13_4 : entry13_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_4 k)) := by decide +kernel

theorem rowsSound13_4 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2532 x
  · exact rowEval2533 x
  · exact rowEval2534 x
  · exact rowEval2535 x
  · exact rowEval2536 x
  · exact rowEval2537 x
  · exact rowEval2538 x
  · exact rowEval2539 x
  · exact rowEval2540 x
  · exact rowEval2541 x
  · exact rowEval2542 x
  · exact rowEval2543 x
  · exact rowEval2544 x
  · exact rowEval2545 x

theorem entryEval13_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_4 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck13_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_4]

def rows13_5 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2546, row2547, row2548, row2549, row2550, row2551, row2552, row2553, row2554, row2555, row2556, row2557, row2558, row2559]

theorem entryCheck13_5 : entry13_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_5 k)) := by decide +kernel

theorem rowsSound13_5 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2546 x
  · exact rowEval2547 x
  · exact rowEval2548 x
  · exact rowEval2549 x
  · exact rowEval2550 x
  · exact rowEval2551 x
  · exact rowEval2552 x
  · exact rowEval2553 x
  · exact rowEval2554 x
  · exact rowEval2555 x
  · exact rowEval2556 x
  · exact rowEval2557 x
  · exact rowEval2558 x
  · exact rowEval2559 x

theorem entryEval13_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_5 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck13_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_5]

def rows13_6 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2560, row2561, row2562, row2563, row2564, row2565, row2566, row2567, row2568, row2569, row2570, row2571, row2572, row2573]

theorem entryCheck13_6 : entry13_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_6 k)) := by decide +kernel

theorem rowsSound13_6 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2560 x
  · exact rowEval2561 x
  · exact rowEval2562 x
  · exact rowEval2563 x
  · exact rowEval2564 x
  · exact rowEval2565 x
  · exact rowEval2566 x
  · exact rowEval2567 x
  · exact rowEval2568 x
  · exact rowEval2569 x
  · exact rowEval2570 x
  · exact rowEval2571 x
  · exact rowEval2572 x
  · exact rowEval2573 x

theorem entryEval13_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_6 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck13_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_6]

def rows13_7 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2574, row2575, row2576, row2577, row2578, row2579, row2580, row2581, row2582, row2583, row2584, row2585, row2586, row2587]

theorem entryCheck13_7 : entry13_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_7 k)) := by decide +kernel

theorem rowsSound13_7 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2574 x
  · exact rowEval2575 x
  · exact rowEval2576 x
  · exact rowEval2577 x
  · exact rowEval2578 x
  · exact rowEval2579 x
  · exact rowEval2580 x
  · exact rowEval2581 x
  · exact rowEval2582 x
  · exact rowEval2583 x
  · exact rowEval2584 x
  · exact rowEval2585 x
  · exact rowEval2586 x
  · exact rowEval2587 x

theorem entryEval13_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_7 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck13_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_7]

def rows13_8 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2588, row2589, row2590, row2591, row2592, row2593, row2594, row2595, row2596, row2597, row2598, row2599, row2600, row2601]

theorem entryCheck13_8 : entry13_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_8 k)) := by decide +kernel

theorem rowsSound13_8 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2588 x
  · exact rowEval2589 x
  · exact rowEval2590 x
  · exact rowEval2591 x
  · exact rowEval2592 x
  · exact rowEval2593 x
  · exact rowEval2594 x
  · exact rowEval2595 x
  · exact rowEval2596 x
  · exact rowEval2597 x
  · exact rowEval2598 x
  · exact rowEval2599 x
  · exact rowEval2600 x
  · exact rowEval2601 x

theorem entryEval13_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_8 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck13_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_8]

def rows13_9 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2602, row2603, row2604, row2605, row2606, row2607, row2608, row2609, row2610, row2611, row2612, row2613, row2614, row2615]

theorem entryCheck13_9 : entry13_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_9 k)) := by decide +kernel

theorem rowsSound13_9 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2602 x
  · exact rowEval2603 x
  · exact rowEval2604 x
  · exact rowEval2605 x
  · exact rowEval2606 x
  · exact rowEval2607 x
  · exact rowEval2608 x
  · exact rowEval2609 x
  · exact rowEval2610 x
  · exact rowEval2611 x
  · exact rowEval2612 x
  · exact rowEval2613 x
  · exact rowEval2614 x
  · exact rowEval2615 x

theorem entryEval13_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_9 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck13_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_9]

def rows13_10 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2616, row2617, row2618, row2619, row2620, row2621, row2622, row2623, row2624, row2625, row2626, row2627, row2628, row2629]

theorem entryCheck13_10 : entry13_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_10 k)) := by decide +kernel

theorem rowsSound13_10 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2616 x
  · exact rowEval2617 x
  · exact rowEval2618 x
  · exact rowEval2619 x
  · exact rowEval2620 x
  · exact rowEval2621 x
  · exact rowEval2622 x
  · exact rowEval2623 x
  · exact rowEval2624 x
  · exact rowEval2625 x
  · exact rowEval2626 x
  · exact rowEval2627 x
  · exact rowEval2628 x
  · exact rowEval2629 x

theorem entryEval13_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_10 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck13_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_10]

def rows13_11 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2630, row2631, row2632, row2633, row2634, row2635, row2636, row2637, row2638, row2639, row2640, row2641, row2642, row2643]

theorem entryCheck13_11 : entry13_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_11 k)) := by decide +kernel

theorem rowsSound13_11 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2630 x
  · exact rowEval2631 x
  · exact rowEval2632 x
  · exact rowEval2633 x
  · exact rowEval2634 x
  · exact rowEval2635 x
  · exact rowEval2636 x
  · exact rowEval2637 x
  · exact rowEval2638 x
  · exact rowEval2639 x
  · exact rowEval2640 x
  · exact rowEval2641 x
  · exact rowEval2642 x
  · exact rowEval2643 x

theorem entryEval13_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_11 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck13_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_11]

def rows13_12 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2644, row2645, row2646, row2647, row2648, row2649, row2650, row2651, row2652, row2653, row2654, row2655, row2656, row2657]

theorem entryCheck13_12 : entry13_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_12 k)) := by decide +kernel

theorem rowsSound13_12 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval2644 x
  · exact rowEval2645 x
  · exact rowEval2646 x
  · exact rowEval2647 x
  · exact rowEval2648 x
  · exact rowEval2649 x
  · exact rowEval2650 x
  · exact rowEval2651 x
  · exact rowEval2652 x
  · exact rowEval2653 x
  · exact rowEval2654 x
  · exact rowEval2655 x
  · exact rowEval2656 x
  · exact rowEval2657 x

theorem entryEval13_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_12 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck13_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_12]

def rows13_13 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2658, row2659, row2660, row2661, row2662, row2663, row2664, row2665, row2666, row2667, row2668, row2669, row2670, row2671]

theorem entryCheck13_13 : entry13_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form13.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form13.terms k).coefficient) (rows13_13 k)) := by decide +kernel

theorem rowsSound13_13 (k : Fin GramFunctions.Block1.form13.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows13_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form13.terms k).tag (GramFunctions.Block1.form13.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval2658 x
  · exact rowEval2659 x
  · exact rowEval2660 x
  · exact rowEval2661 x
  · exact rowEval2662 x
  · exact rowEval2663 x
  · exact rowEval2664 x
  · exact rowEval2665 x
  · exact rowEval2666 x
  · exact rowEval2667 x
  · exact rowEval2668 x
  · exact rowEval2669 x
  · exact rowEval2670 x
  · exact rowEval2671 x

theorem entryEval13_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry13_13 (GramNormalization.eval B) = GramFunctions.Block1.form13.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck13_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form13 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound13_13]

end MUB6.Certificate.GramEntries.Block1

end OAI
