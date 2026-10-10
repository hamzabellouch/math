import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ExposureInterleaving

def grid {n : ℕ} (i : Fin n) : ℝ := (i.val + 1 : ℝ) / n

def countLE (n : ℕ) (x : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => grid i ≤ x)).card

def countLT (n : ℕ) (x : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => grid i < x)).card

theorem grid_pos {n : ℕ} (i : Fin n) : 0 < grid i := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  unfold grid
  positivity

theorem grid_le_one {n : ℕ} (i : Fin n) : grid i ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  rw [grid, div_le_iff₀ hn, one_mul]
  exact_mod_cast Nat.succ_le_iff.mpr i.isLt

theorem grid_strictMono {n : ℕ} : StrictMono (@grid n) := by
  intro i j hij
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  apply (div_lt_div_iff_of_pos_right hn).2
  have h : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  linarith

theorem countLE_eq_floor {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : countLE n x = ⌊(n : ℝ) * x⌋₊ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hnR.le hx
  have hf : ⌊(n : ℝ) * x⌋₊ ≤ n := Nat.floor_le_of_le (by nlinarith)
  have hmem (i : Fin n) : grid i ≤ x ↔ i.val < ⌊(n : ℝ) * x⌋₊ := by
    rw [grid, div_le_iff₀ hnR]
    have hc : (i.val + 1 : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by simp
    rw [hc, mul_comm x, ← Nat.le_floor_iff hnx]
    exact Nat.succ_le_iff
  unfold countLE
  rw [← Finset.card_range ⌊(n : ℝ) * x⌋₊]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr ((hmem i).mp (Finset.mem_filter.mp hi).2)
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    have hjf := Finset.mem_range.mp hj
    let i : Fin n := ⟨j, hjf.trans_le hf⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem i).mpr hjf⟩, rfl⟩

theorem countLT_eq_ceil_sub_one {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx1 : x ≤ 1) : countLT n x = ⌈(n : ℝ) * x⌉₊ - 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ⌈(n : ℝ) * x⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hmem (i : Fin n) : grid i < x ↔ i.val < ⌈(n : ℝ) * x⌉₊ - 1 := by
    rw [grid, div_lt_iff₀ hnR]
    have he : (i.val + 1 : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by simp
    rw [he, mul_comm x, ← Nat.lt_ceil]
    omega
  unfold countLT
  rw [← Finset.card_range (⌈(n : ℝ) * x⌉₊ - 1)]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr ((hmem i).mp (Finset.mem_filter.mp hi).2)
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    have hjc := Finset.mem_range.mp hj
    have hjn : j < n := by omega
    let i : Fin n := ⟨j, hjn⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem i).mpr hjc⟩, rfl⟩

theorem countLE_fraction_error {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |(countLE n x : ℝ) / n - x| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [countLE_eq_floor hn hx hx1, div_sub', abs_div,
    abs_of_pos hnR]
  · exact (div_le_div_iff_of_pos_right hnR).2 <|
      by simpa [mul_comm] using Nat.abs_floor_sub_le (mul_nonneg hnR.le hx)
  · exact hnR.ne'

theorem countLT_fraction_error {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    |(countLT n x : ℝ) / n - x| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 < (n : ℝ) * x := mul_pos hnR hx
  have hc : 1 ≤ ⌈(n : ℝ) * x⌉₊ := Nat.one_le_ceil_iff.mpr hnx
  have hlow := Nat.le_ceil ((n : ℝ) * x)
  have hupp : ((⌈(n : ℝ) * x⌉₊ - 1 : ℕ) : ℝ) < (n : ℝ) * x := by
    apply Nat.lt_ceil.mp
    omega
  rw [countLT_eq_ceil_sub_one hn hx1]
  apply abs_le.mpr
  constructor
  · have h : x - 1 / (n : ℝ) ≤ ((⌈(n : ℝ) * x⌉₊ - 1 : ℕ) : ℝ) / n := by
      apply (le_div_iff₀ hnR).2
      rw [sub_mul, div_mul_cancel₀ _ hnR.ne', Nat.cast_sub hc, Nat.cast_one]
      nlinarith
    linarith
  · have h : ((⌈(n : ℝ) * x⌉₊ - 1 : ℕ) : ℝ) / n - x ≤ 0 := by
      apply sub_nonpos.mpr
      exact (div_le_iff₀ hnR).2 (by nlinarith)
    exact h.trans (by positivity)

def coverGrid {m : ℕ} (γ : ℝ) (i : Fin m) : ℝ := grid i ^ γ⁻¹

theorem coverGrid_pos {m : ℕ} (γ : ℝ) (i : Fin m) : 0 < coverGrid γ i :=
  Real.rpow_pos_of_pos (grid_pos i) _

theorem coverGrid_le_one {m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin m) :
    coverGrid γ i ≤ 1 :=
  Real.rpow_le_one (grid_pos i).le (grid_le_one i) (inv_nonneg.mpr hγ.le)

theorem coverGrid_rpow {m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin m) :
    coverGrid γ i ^ γ = grid i :=
  Real.rpow_inv_rpow (grid_pos i).le hγ.ne'

theorem coverGrid_strictMono {m : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    StrictMono (@coverGrid m γ) := by
  intro i j hij
  exact (Real.rpow_lt_rpow_iff (grid_pos i).le (grid_pos j).le
    (inv_pos.mpr hγ)).2 (grid_strictMono hij)

abbrev Step (n m : ℕ) := Fin n ⊕ Fin m

def parameter {n m : ℕ} (γ : ℝ) : Step n m → ℝ
  | Sum.inl i => grid i
  | Sum.inr j => coverGrid γ j

def Before {n m : ℕ} (γ : ℝ) : Step n m → Step n m → Prop
  | Sum.inl i, Sum.inl j => j < i
  | Sum.inl i, Sum.inr j => coverGrid γ j ≤ grid i
  | Sum.inr i, Sum.inl j => grid j < coverGrid γ i
  | Sum.inr i, Sum.inr j => j < i

def remainingD {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬ Before γ (Sum.inl i) s)

def remainingC {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ¬ Before γ (Sum.inr i) s)

theorem remainingD_at_D {n m : ℕ} (γ : ℝ) (i : Fin n) :
    (remainingD γ (Sum.inl i : Step n m)).card = i.val + 1 := by
  classical
  have hs : remainingD γ (Sum.inl i : Step n m) =
      (Finset.range (i.val + 1)).attachFin (fun j hj =>
        (Finset.mem_range.mp hj).trans_le (Nat.succ_le_iff.mpr i.isLt)) := by
    ext j
    simp only [remainingD, Finset.mem_filter, Finset.mem_univ, true_and,
      Before, not_lt, Finset.mem_attachFin, Finset.mem_range]
    change j.val ≤ i.val ↔ j.val < i.val + 1
    omega
  rw [hs, Finset.card_attachFin, Finset.card_range]

theorem remainingC_at_C {n m : ℕ} (γ : ℝ) (j : Fin m) :
    (remainingC γ (Sum.inr j : Step n m)).card = j.val + 1 := by
  classical
  have hs : remainingC γ (Sum.inr j : Step n m) =
      (Finset.range (j.val + 1)).attachFin (fun i hi =>
        (Finset.mem_range.mp hi).trans_le (Nat.succ_le_iff.mpr j.isLt)) := by
    ext i
    simp only [remainingC, Finset.mem_filter, Finset.mem_univ, true_and,
      Before, not_lt, Finset.mem_attachFin, Finset.mem_range]
    change i.val ≤ j.val ↔ i.val < j.val + 1
    omega
  rw [hs, Finset.card_attachFin, Finset.card_range]

theorem remainingD_at_C {n m : ℕ} (γ : ℝ) (j : Fin m) :
    (remainingD γ (Sum.inr j : Step n m)).card = countLT n (coverGrid γ j) := by
  simp only [remainingD, Before, not_le, countLT]

theorem remainingC_at_D {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (i : Fin n) :
    (remainingC γ (Sum.inl i : Step n m)).card = countLE m (grid i ^ γ) := by
  congr 1
  ext j
  simp only [remainingC, Before, not_lt, Finset.mem_filter,
    Finset.mem_univ, true_and, coverGrid]
  exact Real.rpow_inv_le_iff_of_pos (grid_pos j).le (grid_pos i).le hγ

theorem parameter_pos {n m : ℕ} (γ : ℝ) (s : Step n m) :
    0 < parameter γ s := by
  cases s with
  | inl i => exact grid_pos i
  | inr j => exact coverGrid_pos γ j

theorem parameter_le_one {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (s : Step n m) :
    parameter γ s ≤ 1 := by
  cases s with
  | inl i => exact grid_le_one i
  | inr j => exact coverGrid_le_one hγ j

theorem remainingD_fraction_error {n m : ℕ} (hn : 0 < n)
    {γ : ℝ} (hγ : 0 < γ) (s : Step n m) :
    |((remainingD γ s).card : ℝ) / n - parameter γ s| ≤ 1 / n := by
  cases s with
  | inl i =>
    rw [remainingD_at_D]
    simp only [parameter, grid, Nat.cast_add, Nat.cast_one, sub_self, abs_zero]
    positivity
  | inr j =>
    rw [remainingD_at_C]
    exact countLT_fraction_error hn (coverGrid_pos γ j) (coverGrid_le_one hγ j)

theorem remainingC_fraction_error {n m : ℕ} (hm : 0 < m)
    {γ : ℝ} (hγ : 0 < γ) (s : Step n m) :
    |((remainingC γ s).card : ℝ) / m - parameter γ s ^ γ| ≤ 1 / m := by
  cases s with
  | inl i =>
    rw [remainingC_at_D hγ]
    exact countLE_fraction_error hm (Real.rpow_nonneg (grid_pos i).le _)
      (Real.rpow_le_one (grid_pos i).le (grid_le_one i) hγ.le)
  | inr j =>
    rw [remainingC_at_C]
    change |((j.val + 1 : ℕ) : ℝ) / m - coverGrid γ j ^ γ| ≤ 1 / m
    rw [coverGrid_rpow hγ]
    simp only [grid, Nat.cast_add, Nat.cast_one, sub_self, abs_zero]
    positivity

@[simp] theorem remainingC_zero {n : ℕ} (γ : ℝ) (s : Step n 0) :
    remainingC γ s = ∅ := by
  exact Finset.eq_empty_of_forall_notMem (fun i => Fin.elim0 i)

def typeRank {n m : ℕ} : Step n m → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

theorem before_iff {n m : ℕ} {γ : ℝ} (hγ : 0 < γ) (s t : Step n m) :
    Before γ s t ↔ parameter γ t < parameter γ s ∨
      parameter γ s = parameter γ t ∧ typeRank s < typeRank t := by
  cases s with
  | inl i =>
    cases t with
    | inl j => simp [Before, parameter, typeRank, grid_strictMono.lt_iff_lt]
    | inr j =>
      simp only [Before, parameter, typeRank, Nat.zero_lt_one, and_true]
      exact le_iff_lt_or_eq.trans (or_congr_right eq_comm)
  | inr i =>
    cases t with
    | inl j => simp [Before, parameter, typeRank]
    | inr j =>
      simp [Before, parameter, typeRank, (coverGrid_strictMono hγ).lt_iff_lt]

theorem before_irrefl {n m : ℕ} (γ : ℝ) (s : Step n m) : ¬ Before γ s s := by
  cases s <;> simp [Before]

theorem before_trans {n m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {s t u : Step n m} (hst : Before γ s t) (htu : Before γ t u) :
    Before γ s u := by
  rw [before_iff hγ] at hst htu ⊢
  rcases hst with hst | ⟨hst, hst'⟩ <;> rcases htu with htu | ⟨htu, htu'⟩
  · exact Or.inl (htu.trans hst)
  · exact Or.inl (htu ▸ hst)
  · exact Or.inl (hst ▸ htu)
  · exact Or.inr ⟨hst.trans htu, hst'.trans htu'⟩

theorem before_trichotomy {n m : ℕ} (γ : ℝ) (s t : Step n m) :
    Before γ s t ∨ s = t ∨ Before γ t s := by
  cases s with
  | inl i =>
    cases t with
    | inl j =>
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (congrArg Sum.inl h.symm))
      · exact Or.inr (Or.inr h)
    | inr j =>
      rcases le_or_gt (coverGrid γ j) (grid i) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | inr i =>
    cases t with
    | inl j =>
      rcases lt_or_ge (grid j) (coverGrid γ i) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    | inr j =>
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (congrArg Sum.inr h.symm))
      · exact Or.inr (Or.inr h)

def previousD {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Before γ (Sum.inl i) s)

def previousC {n m : ℕ} (γ : ℝ) (s : Step n m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => Before γ (Sum.inr i) s)

@[simp] theorem currentD_not_previousD {n m : ℕ} (γ : ℝ) (i : Fin n) :
    i ∉ previousD γ (Sum.inl i : Step n m) := by
  simp [previousD, before_irrefl]

@[simp] theorem currentC_not_previousC {n m : ℕ} (γ : ℝ) (i : Fin m) :
    i ∉ previousC γ (Sum.inr i : Step n m) := by
  simp [previousC, before_irrefl]

theorem previousD_add_remainingD {n m : ℕ} (γ : ℝ) (s : Step n m) :
    (previousD γ s).card + (remainingD γ s).card = n := by
  simpa [previousD, remainingD] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => Before γ (Sum.inl i) s))

theorem previousC_add_remainingC {n m : ℕ} (γ : ℝ) (s : Step n m) :
    (previousC γ s).card + (remainingC γ s).card = m := by
  simpa [previousC, remainingC] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => Before γ (Sum.inr i) s))

theorem source_remaining_fraction_bounds {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : Step n m) :
    |((remainingD (Real.sqrt 2) s).card : ℝ) / n - parameter (Real.sqrt 2) s| ≤ 1 / n ∧
    |((remainingC (Real.sqrt 2) s).card : ℝ) / m -
      parameter (Real.sqrt 2) s ^ (Real.sqrt 2)| ≤ 1 / m := by
  have hγ : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact ⟨remainingD_fraction_error hn hγ s, remainingC_fraction_error hm hγ s⟩

end Balanced.ExposureInterleaving

end

end OAI
