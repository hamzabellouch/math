import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Laws

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

def initialMultiplicity (s : Shape) : ℕ :=
  if s 0 = s 1 ∧ s 1 = s 2 then 1 else if s 0 = s 1 ∨ s 1 = s 2 ∨ s 0 = s 2 then 3 else 6

def initialInteger (i : ℕ) : ℤ := assigned (List.range 17) tablea i

def initialWeight (s : Shape) : ℚ :=
  initialMultiplicity s * ∏ i : Fin 3, weight (initialInteger (s i))

def initialLaw (s : Shape) : ℚ :=
  if s ∈ sortedInitial then initialWeight s / (sortedInitial.map initialWeight).sum else 0

theorem initial_table_arguments_bounded : ∀ n ∈ tablea, |n| ≤ 160000 := by decide +kernel

theorem initialWeight_positive (s : Shape) : 0 < initialWeight s := by
  apply mul_pos
  · unfold initialMultiplicity
    split_ifs <;> norm_num
  · apply Finset.prod_pos
    intro i _
    apply weight_positive_of_argument_bound
    exact assigned_argument_bound _ tablea initial_table_arguments_bounded _

theorem initialLaw_positive (s : Shape) (hs : s ∈ sortedInitial) : 0 < initialLaw s := by
  rw [initialLaw, ite_eq_left hs]
  apply div_pos (initialWeight_positive s)
  exact list_sum_map_positive _ _ (by decide +kernel) (fun t _ => initialWeight_positive t)

theorem initialLaw_normalized : (sortedInitial.map initialLaw).sum = 1 := by
  have he : sortedInitial.map initialLaw = sortedInitial.map
      (fun s => initialWeight s / (sortedInitial.map initialWeight).sum) := by
    apply List.map_congr_left
    intro s hs
    simp only [initialLaw, hs, ite_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive _ _ (by decide +kernel)
    (fun s _ => initialWeight_positive s))

theorem binary_table_bounds : ∀ n ∈ tabled, 0 ≤ n ∧ n ≤ 110106 := by decide +kernel

theorem binaryInteger_bounds (t u : Shape) :
    0 ≤ binaryInteger t u ∧ binaryInteger t u ≤ 110106 := by
  rcases assigned_mem_or_zero binaryKeys tabled (t, u) with h | h
  · change 0 ≤ assigned binaryKeys tabled (t, u) ∧ assigned binaryKeys tabled (t, u) ≤ 110106
    rw [h]
    norm_num
  · exact binary_table_bounds _ h

theorem binaryParameter_bounds (t u : Shape) :
    0 ≤ binaryParameter t u ∧ binaryParameter t u ≤ (110106 : ℚ) / 1000000 := by
  obtain ⟨hlo, hhi⟩ := binaryInteger_bounds t u
  have hl : (0 : ℚ) ≤ binaryInteger t u := by exact_mod_cast hlo
  have hh : (binaryInteger t u : ℚ) ≤ 110106 := by exact_mod_cast hhi
  unfold binaryParameter
  constructor
  · exact div_nonneg hl (by norm_num)
  · exact div_le_div_of_nonneg_right hh (by norm_num)

def singletonSlot (k : ℕ) : Fin 6 :=
  match k with
  | 0 => 0
  | 1 => 1
  | 3 => 4
  | 4 => 5
  | _ => 0

def littleLaw (t u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - binaryParameter t u else if i = 3 then binaryParameter t u else 0
  else if i = singletonSlot (u w) then 1 else 0

theorem littleLaw_nonnegative (t u : Shape) (w : Fin 3) (i : Fin 6) :
    0 ≤ littleLaw t u w i := by
  obtain ⟨hl, hh⟩ := binaryParameter_bounds t u
  unfold littleLaw
  split_ifs <;> linarith

theorem littleLaw_normalized (t u : Shape) (w : Fin 3) :
    ∑ i : Fin 6, littleLaw t u w i = 1 := by
  by_cases h : u w = 2
  · simp only [littleLaw, h, ite_true]
    calc
      _ = ∑ i : Fin 6, ((if i = 2 then 1 - binaryParameter t u else 0) +
          (if i = 3 then binaryParameter t u else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = 2
        · subst i
          simp [show (2 : Fin 6) ≠ 3 by decide]
        · simp [hi]
      _ = 1 := by simp [Finset.sum_add_distrib]
  · simp [littleLaw, h]

theorem orderedPairWeight_positive (t : Shape) (i j : Fin 6) :
    0 < weight (orderedPairInteger t i j) := by
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ tablez zero_table_arguments_bounded _

theorem orderedPairs_nonempty : ∀ t ∈ zeroSecond, orderedPairs t ≠ [] := by decide +kernel

theorem orderedPairs_support (t : Shape) (ij : PairSlot) (h : ij ∈ orderedPairs t) :
    statisticWeight ij.1 + statisticWeight ij.2 = shapeMax t := by
  simp only [orderedPairs, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨i, _, j, _, he⟩ := h
  split_ifs at he with hs
  · cases Option.some.inj he
    exact hs

theorem zeroPairLaw_positive (t : Shape) (ht : t ∈ zeroSecond) (ij : PairSlot)
    (hij : ij ∈ orderedPairs t) : 0 < zeroPairLaw t ij.1 ij.2 := by
  rw [zeroPairLaw, ite_eq_left (orderedPairs_support t ij hij)]
  exact div_pos (orderedPairWeight_positive _ _ _)
    (list_sum_map_positive _ _ (orderedPairs_nonempty t ht)
      (fun p _ => orderedPairWeight_positive t p.1 p.2))

theorem zeroPairLaw_normalized (t : Shape) (ht : t ∈ zeroSecond) :
    ((orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2)).sum = 1 := by
  have he : (orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2) =
      (orderedPairs t).map (fun ij => weight (orderedPairInteger t ij.1 ij.2) /
        ((orderedPairs t).map (fun p => weight (orderedPairInteger t p.1 p.2))).sum) := by
    apply List.map_congr_left
    intro ij hij
    simp only [zeroPairLaw, orderedPairs_support t ij hij, ite_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive _ _ (orderedPairs_nonempty t ht)
    (fun p _ => orderedPairWeight_positive t p.1 p.2))

end MatrixMultiplication.AllFieldParameters

end OAI
