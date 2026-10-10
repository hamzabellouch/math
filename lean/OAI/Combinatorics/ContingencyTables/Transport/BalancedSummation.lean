import OAI.Combinatorics.ContingencyTables.Transport.QuadraticTransport
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Balanced-pair summation of two-removal forms

This is the finite unweighted closure step in paper 200-01,
Lemma `lem:pair-summation` (`D'=B`), and paper 200-02,
Lemma `lem:integer-signature`. The hypotheses describe the actual old/fresh
blocks and their adjacent cross entries. Cumulative coefficients are
constructed from those cross entries; no transport or closure conclusion is
assumed. In particular the zero-diagonal capacity-two case is included.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

/-- The lower endpoint convention used by the balanced-pair matrices. -/
theorem sum_pred_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (2 * a j - a (j - 1) - a (j + 1))) =
      a n - a (n + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- First moment of the discrete second difference, with exact boundaries. -/
theorem sum_firstMoment_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (j : ℝ) * (2 * a j - a (j - 1) - a (j + 1))) =
      ((n : ℝ) + 1) * a n - a 0 - (n : ℝ) * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- Second moment of the same difference. -/
theorem sum_secondMoment_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (j : ℝ) ^ 2 * (2 * a j - a (j - 1) - a (j + 1))) =
      ((n : ℝ) + 1) ^ 2 * a n - (n : ℝ) ^ 2 * a (n + 1) + a 0 -
        2 * ∑ j ∈ Finset.range (n + 1), a j := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have hs : (∑ j ∈ Finset.range (n + 1 + 1), a j) =
        (∑ j ∈ Finset.range (n + 1), a j) + a (n + 1) := Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, ih, hs]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- The exact weighted telescope in equation pair-weighted. The boundary
terms are scalar values, so invalid endpoint matrices are never needed. -/
theorem sum_weighted_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) *
      (2 * a j - a (j - 1) - a (j + 1))) =
      2 * (∑ j ∈ Finset.range (n + 1), a j) - ((n : ℝ) + 1) * (a 0 + a n) := by
  calc
    _ = (n : ℝ) * (∑ j ∈ Finset.range (n + 1), (j : ℝ) *
          (2 * a j - a (j - 1) - a (j + 1))) -
        ∑ j ∈ Finset.range (n + 1), (j : ℝ) ^ 2 *
          (2 * a j - a (j - 1) - a (j + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [sum_firstMoment_second_differences, sum_secondMoment_second_differences]
      ring

/-- Summation of the local inequalities with the actual nonnegative
weights. Only interior inequalities are required. -/
theorem weighted_second_differences_bound (a v : ℕ → ℝ) (n : ℕ)
    (ha0 : a 0 = 0) (han : a n = 0)
    (hlocal : ∀ j, 0 < j → j < n →
      2 * a j - a (j - 1) - a (j + 1) ≤ -v j) :
    2 * (∑ j ∈ Finset.range (n + 1), a j) ≤
      -(∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) * v j) := by
  have hsum : (∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) *
      (2 * a j - a (j - 1) - a (j + 1))) ≤
      ∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) * (-v j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp
    by_cases hjeq : j = n
    · subst j
      simp
    have hjr : (j : ℝ) ≤ n := by exact_mod_cast hjn
    apply mul_le_mul_of_nonneg_left (hlocal j (by omega) (by omega))
    exact mul_nonneg (Nat.cast_nonneg j) (sub_nonneg.mpr hjr)
  rw [sum_weighted_second_differences, ha0, han] at hsum
  simp only [add_zero, mul_zero, sub_zero, mul_neg, Finset.sum_neg_distrib] at hsum
  exact hsum

section Cumulative

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The partial cross-entry sum in equation pair-cumulative. -/
def pairCumulative (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range j, S (l + 1) v

lemma pairCumulative_zero (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) : pairCumulative S v 0 = 0 := by
  simp [pairCumulative]

lemma pairCumulative_succ (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) (j : ℕ) :
    pairCumulative S v (j + 1) = pairCumulative S v j + S (j + 1) v := by
  exact Finset.sum_range_succ _ _

/-- The cumulative coefficients, with division by zero harmless at the
endpoints because the corresponding cumulative mass is proved zero. -/
noncomputable def pairCoefficient (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ) (v : V) (j : ℕ) : ℝ :=
  pairCumulative S v j / u j

lemma pairCoefficient_represents (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ)
    (n : ℕ) (v : V)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hbalance : pairCumulative S v n = 0) (hend : S (n + 1) v = 0)
    {j : ℕ} (hj : j ≤ n + 1) :
    u j * pairCoefficient S u v j = pairCumulative S v j := by
  by_cases hj0 : j = 0
  · subst j
    simp [pairCoefficient, pairCumulative_zero]
  by_cases hjn : j = n
  · subst j
    simp [pairCoefficient, hbalance]
  by_cases hjn1 : j = n + 1
  · subst j
    simp [pairCoefficient, pairCumulative_succ, hbalance, hend]
  have hu : u j ≠ 0 := ne_of_gt (huint j (by omega) (by omega))
  dsimp [pairCoefficient]
  field_simp

/-- Representation up to the balanced endpoint needs no value outside
that endpoint. This version is used for the `D'=B+1` interior displays. -/
lemma pairCoefficient_represents_le (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ)
    (n : ℕ) (v : V)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hbalance : pairCumulative S v n = 0) {j : ℕ} (hj : j ≤ n) :
    u j * pairCoefficient S u v j = pairCumulative S v j := by
  by_cases hj0 : j = 0
  · subst j
    simp [pairCoefficient, pairCumulative_zero]
  by_cases hjn : j = n
  · subst j
    simp [pairCoefficient, hbalance]
  have hu : u j ≠ 0 := ne_of_gt (huint j (by omega) (by omega))
  dsimp [pairCoefficient]
  field_simp

lemma pairCumulative_difference (S : ℕ → V →ₗ[ℝ] ℝ) (v : V) {j : ℕ} (hj : 0 < j) :
    pairCumulative S v j - pairCumulative S v (j - 1) = S j v := by
  have hh := pairCumulative_succ S v (j - 1)
  have hj' : j - 1 + 1 = j := by omega
  rw [hj'] at hh
  linarith

end Cumulative

section Closure

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Summing the old blocks of the two-removal matrices preserves the
one-positive-direction signature. The cumulative coefficients and common kernel are explicit. -/
theorem balancedPair_sum_onePositive
    (n : ℕ) (hn : 2 ≤ n)
    (B : ℕ → BilinForm ℝ W) (old : V →ₗ[ℝ] W) (ea eb : W)
    (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ)
    (hsymm : ∀ j ≤ n, ∀ x y, B j x y = B j y x)
    (hsig : ∀ j ≤ n, OnePositiveDirection (B j))
    (hu0 : u 0 = 0) (hun : u n = 0) (hun1 : u (n + 1) = 0)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hS0 : S 0 = 0) (hSn1 : S (n + 1) = 0)
    (haa : ∀ j ≤ n, B j ea ea = u (j - 1))
    (hbb : ∀ j ≤ n, B j eb eb = u (j + 1))
    (hab : ∀ j ≤ n, B j ea eb = u j)
    (hha : ∀ j ≤ n, ∀ v, B j (old v) ea = S j v)
    (hhb : ∀ j ≤ n, ∀ v, B j (old v) eb = S (j + 1) v) :
    OnePositiveDirection (∑ j ∈ Finset.range (n + 1), (B j).compl₁₂ old old) := by
  let A : BilinForm ℝ V := ∑ j ∈ Finset.range (n + 1), (B j).compl₁₂ old old
  let L : V →ₗ[ℝ] ℝ := ∑ j ∈ Finset.range n, S (j + 1)
  have hA (v w : V) : A v w = ∑ j ∈ Finset.range (n + 1), B j (old v) (old w) := by
    simp only [A, LinearMap.sum_apply, LinearMap.compl₁₂_apply]
  have hu_nonneg {j : ℕ} (hj : j ≤ n + 1) : 0 ≤ u j := by
    by_cases hj0 : j = 0
    · simp [hj0, hu0]
    by_cases hjn : j = n
    · simp [hjn, hun]
    by_cases hjn1 : j = n + 1
    · simp [hjn1, hun1]
    exact le_of_lt (huint j (by omega) (by omega))
  change OnePositiveDirection A
  refine onePositiveDirection_of_kernel A ?_ L ?_
  · intro v w
    rw [hA, hA]
    apply Finset.sum_congr rfl
    intro j hj
    exact hsymm j (by simpa using Finset.mem_range.mp hj) _ _
  · intro v hv
    have hbalance : pairCumulative S v n = 0 := by
      simpa only [L, LinearMap.sum_apply, pairCumulative] using hv
    have hend : S (n + 1) v = 0 := by rw [hSn1]; rfl
    let g := pairCoefficient S u v
    have hrepr {j : ℕ} (hj : j ≤ n + 1) : u j * g j = pairCumulative S v j :=
      pairCoefficient_represents S u n v huint hbalance hend hj
    have hlocal {j : ℕ} (hj : j ≤ n) :
        2 * (u j * g j ^ 2) - (u (j - 1) * g (j - 1) ^ 2) -
          (u (j + 1) * g (j + 1) ^ 2) ≤ -B j (old v) (old v) := by
      have hleft : B j (old v) ea = u j * g j - u (j - 1) * g (j - 1) := by
        rw [hha j hj, hrepr (by omega), hrepr (by omega)]
        by_cases hj0 : j = 0
        · subst j
          simp [hS0, pairCumulative_zero]
        · have hc := pairCumulative_succ S v (j - 1)
          have heq : j - 1 + 1 = j := by omega
          rw [heq] at hc
          linarith
      have hright : B j (old v) eb = u (j + 1) * g (j + 1) - u j * g j := by
        rw [hhb j hj, hrepr (by omega), hrepr (by omega), pairCumulative_succ]
        ring
      have hpositive : 0 < u (j - 1) ∨ 0 < u (j + 1) ∨
          (u (j - 1) = 0 ∧ u (j + 1) = 0 ∧ 0 < u j) := by
        by_cases hm : 0 < u (j - 1)
        · exact Or.inl hm
        by_cases hp : 0 < u (j + 1)
        · exact Or.inr (Or.inl hp)
        have hj0 : 0 < j := by
          by_contra h
          have hjz : j = 0 := by omega
          subst j
          exact hp (huint 1 (by omega) (by omega))
        have hjn : j < n := by
          by_contra h
          have hjeq : j = n := by omega
          subst j
          exact hm (huint (n - 1) (by omega) (by omega))
        exact Or.inr (Or.inr ⟨le_antisymm (le_of_not_gt hm) (hu_nonneg (by omega)),
          le_antisymm (le_of_not_gt hp) (hu_nonneg (by omega)), huint j hj0 hjn⟩)
      simpa only [mul_assoc] using pair_step_of_signature (B j) (hsymm j hj) (hsig j hj) (old v) ea eb
        (u (j - 1)) (u j) (u (j + 1)) (g (j - 1)) (g j) (g (j + 1))
        (haa j hj) (hbb j hj) (hab j hj) hleft hright
        (hu_nonneg (by omega)) (hu_nonneg (by omega)) hpositive
    have hsum := Finset.sum_le_sum (s := Finset.range (n + 1))
      (fun j hj => hlocal (by simpa using Finset.mem_range.mp hj))
    rw [sum_pred_second_differences] at hsum
    simp only [hun, hun1, zero_mul, sub_self, Finset.sum_neg_distrib] at hsum
    rw [hA]
    linarith

/-- The actual weighted pair estimate (`D'=B+1`) used in integer
signed transport. Only the box-valid interior matrices are evaluated.
The coefficients are the explicitly constructed cumulative quotients. -/
theorem balancedPair_weighted_potential
    (n : ℕ) (B : ℕ → BilinForm ℝ W) (old : V →ₗ[ℝ] W) (ea eb : W)
    (S : ℕ → V →ₗ[ℝ] ℝ) (u : ℕ → ℝ) (v : V)
    (hsymm : ∀ j, 0 < j → j < n → ∀ x y, B j x y = B j y x)
    (hsig : ∀ j, 0 < j → j < n → OnePositiveDirection (B j))
    (hu0 : u 0 = 0) (hun : u n = 0)
    (huint : ∀ j, 0 < j → j < n → 0 < u j)
    (hbalance : pairCumulative S v n = 0)
    (haa : ∀ j, 0 < j → j < n → B j ea ea = u (j - 1))
    (hbb : ∀ j, 0 < j → j < n → B j eb eb = u (j + 1))
    (hab : ∀ j, 0 < j → j < n → B j ea eb = u j)
    (hha : ∀ j, 0 < j → j < n → B j (old v) ea = S j v)
    (hhb : ∀ j, 0 < j → j < n → B j (old v) eb = S (j + 1) v) :
    2 * (∑ j ∈ Finset.range (n + 1), u j * pairCoefficient S u v j ^ 2) ≤
      -(∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) * B j (old v) (old v)) := by
  let g := pairCoefficient S u v
  have hrepr {j : ℕ} (hj : j ≤ n) : u j * g j = pairCumulative S v j :=
    pairCoefficient_represents_le S u n v huint hbalance hj
  have hu_nonneg {j : ℕ} (hj : j ≤ n) : 0 ≤ u j := by
    by_cases hj0 : j = 0
    · simp [hj0, hu0]
    by_cases hjn : j = n
    · simp [hjn, hun]
    exact le_of_lt (huint j (by omega) (by omega))
  apply weighted_second_differences_bound
    (fun j => u j * g j ^ 2) (fun j => B j (old v) (old v)) n
    (by simp [hu0]) (by simp [hun])
  intro j hj0 hjn
  have hleft : B j (old v) ea = u j * g j - u (j - 1) * g (j - 1) := by
    rw [hha j hj0 hjn, hrepr (by omega), hrepr (by omega)]
    exact (pairCumulative_difference S v hj0).symm
  have hright : B j (old v) eb = u (j + 1) * g (j + 1) - u j * g j := by
    rw [hhb j hj0 hjn, hrepr (by omega), hrepr (by omega), pairCumulative_succ]
    ring
  have hpositive : 0 < u (j - 1) ∨ 0 < u (j + 1) ∨
      (u (j - 1) = 0 ∧ u (j + 1) = 0 ∧ 0 < u j) := by
    by_cases hm : 0 < u (j - 1)
    · exact Or.inl hm
    by_cases hp : 0 < u (j + 1)
    · exact Or.inr (Or.inl hp)
    exact Or.inr (Or.inr ⟨le_antisymm (le_of_not_gt hm) (hu_nonneg (by omega)),
      le_antisymm (le_of_not_gt hp) (hu_nonneg (by omega)), huint j hj0 hjn⟩)
  simpa only [mul_assoc] using pair_step_of_signature (B j) (hsymm j hj0 hjn) (hsig j hj0 hjn)
    (old v) ea eb (u (j - 1)) (u j) (u (j + 1)) (g (j - 1)) (g j) (g (j + 1))
    (haa j hj0 hjn) (hbb j hj0 hjn) (hab j hj0 hjn) hleft hright
    (hu_nonneg (by omega)) (hu_nonneg (by omega)) hpositive

end Closure

end ContingencyTables

end OAI
