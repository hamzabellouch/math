import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteKernel

variable {α : Type*} [Fintype α]

theorem energy_eq_pairwise
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (f : α → ℝ) :
    (∑ i, f i * (f i - ∑ j, K i j * f j)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, K i j * (f i - f j) ^ 2 := by
  have hcol (j : α) : ∑ i, K i j = 1 := by
    simpa only [hsymm] using hrow j
  have hleft : (∑ i, ∑ j, K i j * f i ^ 2) = ∑ i, f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_mul, hrow, one_mul]
  have hright : (∑ i, ∑ j, K i j * f j ^ 2) = ∑ j, f j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_mul, hcol, one_mul]
  have hexpand :
      (∑ i, ∑ j, K i j * (f i - f j) ^ 2) =
        (∑ i, ∑ j, K i j * f i ^ 2) +
        (∑ i, ∑ j, K i j * f j ^ 2) -
        2 * ∑ i, f i * (∑ j, K i j * f j) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexpand, hleft, hright]
  simp only [mul_sub, ← pow_two, Finset.sum_sub_distrib]
  ring

theorem energy_nonneg
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (f : α → ℝ) :
    0 ≤ ∑ i, f i * (f i - ∑ j, K i j * f j) := by
  rw [energy_eq_pairwise K hrow hsymm f]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hpos i j) (sq_nonneg _))))

theorem energy_eq_zero_iff
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (f : α → ℝ) :
    (∑ i, f i * (f i - ∑ j, K i j * f j)) = 0 ↔
      ∀ i j, 0 < K i j → f i = f j := by
  have hterm (i j : α) : 0 ≤ K i j * (f i - f j) ^ 2 :=
    mul_nonneg (hpos i j) (sq_nonneg _)
  rw [energy_eq_pairwise K hrow hsymm f]
  constructor
  · intro h i j hij
    have hsum : (∑ i, ∑ j, K i j * (f i - f j) ^ 2) = 0 := by
      linarith
    have hi : (∑ j, K i j * (f i - f j) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        Finset.sum_nonneg (fun b _ => hterm a b))).mp hsum i (Finset.mem_univ i)
    have hijzero : K i j * (f i - f j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hterm i b)).mp hi j
        (Finset.mem_univ j)
    have hsquare : (f i - f j) ^ 2 = 0 :=
      (mul_eq_zero.mp hijzero).resolve_left (ne_of_gt hij)
    nlinarith [sq_nonneg (f i - f j)]
  · intro h
    have hzero (i j : α) : K i j * (f i - f j) ^ 2 = 0 := by
      by_cases hij : K i j = 0
      · simp [hij]
      · have hEq := h i j (lt_of_le_of_ne (hpos i j) (Ne.symm hij))
        simp [hEq]
    simp [hzero]

theorem eq_of_energy_eq_zero_of_reachable
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (f : α → ℝ)
    (hzero : (∑ i, f i * (f i - ∑ j, K i j * f j)) = 0)
    {i j : α}
    (hpath : Relation.ReflTransGen (fun a b => 0 < K a b) i j) :
    f i = f j := by
  have hlocal := (energy_eq_zero_iff K hrow hsymm hpos f).mp hzero
  induction hpath with
  | refl => rfl
  | @tail b c hab hbc ih => exact ih.trans (hlocal b c hbc)

theorem weighted_sq_sum_le
    (w f : α → ℝ)
    (hpos : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (∑ i, w i * f i) ^ 2 ≤ ∑ i, w i * f i ^ 2 := by
  let m := ∑ i, w i * f i
  have hvar : 0 ≤ ∑ i, w i * (f i - m) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hpos i) (sq_nonneg _))
  have heq : (∑ i, w i * (f i - m) ^ 2) =
      (∑ i, w i * f i ^ 2) - m ^ 2 := by
    calc
      (∑ i, w i * (f i - m) ^ 2) =
          ∑ i, (w i * f i ^ 2 - 2 * m * (w i * f i) + w i * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, w i * f i ^ 2) - m ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, hsum]
        change (∑ i, w i * f i ^ 2) - 2 * m * m + 1 * m ^ 2 = _
        ring
  rw [heq] at hvar
  dsimp [m] at hvar
  linarith

theorem sq_sum_apply_le
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (f : α → ℝ) :
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤ ∑ i, f i ^ 2 := by
  have hcol (j : α) : ∑ i, K i j = 1 := by
    simpa only [hsymm] using hrow j
  calc
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤ ∑ i, ∑ j, K i j * f j ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact weighted_sq_sum_le (K i) f (hpos i) (hrow i)
    _ = ∑ i, f i ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, hcol, one_mul]

theorem lazy_sq_sum_apply_le_inner
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (hlazy : ∀ i, (1 / 2 : ℝ) ≤ K i i)
    (f : α → ℝ) :
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤
      ∑ i, f i * (∑ j, K i j * f j) := by
  classical
  let Q (i j : α) : ℝ := 2 * K i j - if i = j then 1 else 0
  have hQrow (i : α) : ∑ j, Q i j = 1 := by
    norm_num [Q, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow]
  have hQsymm (i j : α) : Q i j = Q j i := by
    simp only [Q, hsymm i j, eq_comm]
  have hQpos (i j : α) : 0 ≤ Q i j := by
    by_cases hij : i = j
    · subst j
      simp only [Q, ite_true]
      linarith [hlazy i]
    · simp only [Q, hij, ite_false, sub_zero]
      exact mul_nonneg (by norm_num) (hpos i j)
  have hQapply (i : α) :
      (∑ j, Q i j * f j) = 2 * (∑ j, K i j * f j) - f i := by
    simp [Q, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have hc := sq_sum_apply_le Q hQrow hQsymm hQpos f
  simp only [hQapply] at hc
  have hexpand : (∑ i, (2 * (∑ j, K i j * f j) - f i) ^ 2) =
      4 * (∑ i, (∑ j, K i j * f j) ^ 2) -
      4 * (∑ i, f i * (∑ j, K i j * f j)) + ∑ i, f i ^ 2 := by
    calc
      _ = ∑ i, (4 * (∑ j, K i j * f j) ^ 2 -
          4 * (f i * (∑ j, K i j * f j)) + f i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexpand] at hc
  linarith

theorem lazy_inner_nonneg
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (hlazy : ∀ i, (1 / 2 : ℝ) ≤ K i i)
    (f : α → ℝ) :
    0 ≤ ∑ i, f i * (∑ j, K i j * f j) :=
  le_trans (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (lazy_sq_sum_apply_le_inner K hrow hsymm hpos hlazy f)

end Problem315.FiniteKernel

end

end OAI
