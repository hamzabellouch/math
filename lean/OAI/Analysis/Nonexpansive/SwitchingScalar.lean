import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Scalar estimates for finite leaf switching

The first estimates telescope the actual scaled ancestor recurrence.  The
second estimates bound a finite dyadic tolerance tail, including an empty
tail.  These lemmas involve only real scalars and finite sums; the switching
construction supplies their hypotheses from its actual maps and weights.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- Multiplying the one-step displacement estimate by the parent weight
produces the telescoping form, using the actual child-weight equation. -/
theorem scaled_path_step {w w' a a' α δ : ℝ}
    (hw : 0 ≤ w) (hchild : w' = w * α)
    (hstep : a ≤ α * a' + (1 - α) + δ) :
    w * a ≤ w' * a' + w - w' + w * δ := by
  calc
    w * a ≤ w * (α * a' + (1 - α) + δ) :=
      mul_le_mul_of_nonneg_left hstep hw
    _ = w' * a' + w - w' + w * δ := by rw [hchild]; ring

/-- The scaled finite path recurrence telescopes without division by weights.
This identity needs no positive lower bound on any path weight. -/
theorem scaled_path_telescope (W A δ : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ i < k,
      W i * A i ≤ W (i + 1) * A (i + 1) + W i - W (i + 1) + W i * δ i) :
    W 0 * A 0 ≤ W k * A k + W 0 - W k +
      ∑ i ∈ Finset.range k, W i * δ i := by
  revert hstep
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hstep
      have hprev := ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self k)))
      have hlast := hstep k (Nat.lt_succ_self k)
      rw [Finset.sum_range_succ]
      linarith

/-- The root displacement bound used before a whole descendant block switches.
Both the terminal displacement and the unweighted ancestor error budget are
at most `e`; path weights lie in the unit interval. -/
theorem before_block_scalar_le (W A δ : ℕ → ℝ) (k : ℕ) (e : ℝ)
    (hroot : W 0 = 1)
    (hW : ∀ i ≤ k, 0 ≤ W i ∧ W i ≤ 1)
    (he : 0 ≤ e) (hterminal : A k ≤ e)
    (hδ : ∀ i < k, 0 ≤ δ i)
    (hbudget : ∑ i ∈ Finset.range k, δ i ≤ e)
    (hstep : ∀ i < k,
      W i * A i ≤ W (i + 1) * A (i + 1) + W i - W (i + 1) + W i * δ i) :
    A 0 ≤ 1 - W k + 2 * e := by
  have hterminal' : W k * A k ≤ e := by
    calc
      W k * A k ≤ W k * e := mul_le_mul_of_nonneg_left hterminal (hW k le_rfl).1
      _ ≤ 1 * e := mul_le_mul_of_nonneg_right (hW k le_rfl).2 he
      _ = e := one_mul e
  have hweighted : (∑ i ∈ Finset.range k, W i * δ i) ≤ e := by
    calc
      (∑ i ∈ Finset.range k, W i * δ i) ≤ ∑ i ∈ Finset.range k, δ i := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hW i (Nat.le_of_lt hik)).2 (hδ i hik)
      _ ≤ e := hbudget
  have htel : A 0 ≤ W k * A k + 1 - W k +
      ∑ i ∈ Finset.range k, W i * δ i := by
    simpa only [hroot, one_mul] using scaled_path_telescope W A δ k hstep
  linarith

/-- Exact finite geometric sum for the dyadic tolerance coefficients. -/
theorem dyadic_sum_range (N : ℕ) :
    (∑ d ∈ Finset.range N, (1 / 2 : ℝ) ^ (d + 1)) = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [pow_succ]
      ring

/-- Exact finite dyadic tail, including the endpoint term that is discarded
in the later upper bound. -/
theorem dyadic_sum_Ico (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1)) =
      (1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ N := by
  rw [Finset.sum_Ico_eq_sub _ hkN, dyadic_sum_range, dyadic_sum_range]
  ring

/-- A nonnegative decreasing budget schedule bounds every finite dyadic
tolerance tail.  No infinite series or limiting interchange is used. -/
theorem dyadic_weighted_tail_le (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
      (1 / 2 : ℝ) ^ k * M k := by
  calc
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
        ∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M k := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hM_anti (Finset.mem_Ico.mp hd).1)
        (pow_nonneg (by norm_num) _)
    _ = ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ N) * M k := by
      rw [← Finset.sum_mul, dyadic_sum_Ico k N hkN]
    _ ≤ (1 / 2 : ℝ) ^ k * M k := by
      apply mul_le_mul_of_nonneg_right _ (hM_nonneg k)
      exact sub_le_self _ (pow_nonneg (by norm_num) _)

/-- The same finite tail is at most the budget at its initial level. -/
theorem dyadic_weighted_tail_le_initial (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤ M k := by
  calc
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
        (1 / 2 : ℝ) ^ k * M k :=
      dyadic_weighted_tail_le M hM_nonneg hM_anti k N hkN
    _ ≤ 1 * M k := mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) (hM_nonneg k)
    _ = M k := one_mul _

/-- Uniform comparison with any particular node budget at the same level. -/
theorem dyadic_weighted_tail_le_budget (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k N : ℕ) (hkN : k ≤ N) {e : ℝ} (hbudget : M k ≤ e) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤ e :=
  (dyadic_weighted_tail_le_initial M hM_nonneg hM_anti k N hkN).trans hbudget

end ReflexiveFixedPoints

end OAI
