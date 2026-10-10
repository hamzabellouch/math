import Mathlib.Topology.Algebra.InfiniteSum.Real
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteInverseSquareDensity
import OAI.NumberTheory.Ostmann.ZeroDensity.HighZeroTailBound

namespace OAI

/-! # Convergence of inverse-square weights from the ordinary zero count -/

namespace Ostmann

open scoped Classical BigOperators

private theorem zero_height_log_three_halves {ι : Type*} (S : Finset ι) (h : ι → ℝ)
    (Q K : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hh : ∀ i ∈ S, 0 ≤ h i)
    (hcount : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    ∀ s : ℝ, 0 ≤ s →
      ((S.filter (fun i => Real.log (1 + h i) ≤ s)).card : ℝ) ≤
        (2 * K * (Real.log Q + 5)) * Real.exp ((3 / 2) * s) := by
  intro s hs
  have hQp : 0 < Q := by linarith
  have he : 1 ≤ Real.exp s := Real.one_le_exp hs
  have hhf : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hsub : S.filter (fun i => Real.log (1 + h i) ≤ s) ⊆
      S.filter (fun i => h i ≤ Real.exp s) := by
    intro i hi
    obtain ⟨hiS, hi⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hiS, ?_⟩
    have hex := (Real.log_le_iff_le_exp (by linarith [hh i hiS] : 0 < 1 + h i)).mp hi
    linarith
  have hlog : Real.log (Q * (Real.exp s + 2)) ≤
      (Real.log Q + 5) * Real.exp (s / 2) := by
    rw [Real.log_mul hQp.ne' (by positivity : Real.exp s + 2 ≠ 0)]
    have hinside : Real.exp s + 2 ≤ 3 * Real.exp s := by linarith
    have hl := Real.log_le_log (by positivity : 0 < Real.exp s + 2) hinside
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hl
    have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have hs' := Real.add_one_le_exp (s / 2)
    have hq := mul_le_mul_of_nonneg_left hhf (by linarith : 0 ≤ Real.log Q + 3)
    nlinarith
  have hl0 : 0 ≤ Real.log (Q * (Real.exp s + 2)) := Real.log_nonneg (by nlinarith)
  calc
    _ ≤ ((S.filter (fun i => h i ≤ Real.exp s)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (Real.exp s + 1) * Real.log (Q * (Real.exp s + 2)) :=
      hcount (Real.exp s) (Real.exp_nonneg _)
    _ ≤ (K * (2 * Real.exp s)) * ((Real.log Q + 5) * Real.exp (s / 2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hK
      · exact hlog
      · exact hl0
      · positivity
    _ = (2 * K * (Real.log Q + 5)) * Real.exp ((3 / 2) * s) := by
      rw [show (3 / 2 : ℝ) * s = s + s / 2 by ring, Real.exp_add]
      ring

/-- Only the ordinary O(T log T) count is needed, not a zero-free region. -/
theorem inverse_square_weights_summable {ι : Type*} (h : ι → ℝ)
    (Q K : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hh : ∀ i, 0 ≤ h i)
    (hcount : ∀ (S : Finset ι) (t : ℝ), 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    Summable (fun i => ((1 + h i) ^ 2)⁻¹) := by
  let B := 2 * K * (Real.log Q + 5)
  let f : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ (-4 / 3 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity [Real.log_nonneg hQ]
  have hf : Summable f := by
    have ht := (Real.summable_nat_rpow.mpr (by norm_num : (-4 / 3 : ℝ) < -1))
    simpa only [f, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr ht
  have he (i : ι) : Real.exp (-2 * Real.log (1 + h i)) = ((1 + h i) ^ 2)⁻¹ := by
    rw [show -2 * Real.log (1 + h i) = -(Real.log (1 + h i) + Real.log (1 + h i)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log (by linarith [hh i] : 0 < 1 + h i), pow_two]
  apply summable_of_sum_le (fun i => by positivity) (c := B ^ (4 / 3 : ℝ) * ∑' j, f j)
  intro S
  have hb := finite_exp_three_halves_sum S (fun i => Real.log (1 + h i)) B hB
    (fun i _ => Real.log_nonneg (by linarith [hh i]))
    (zero_height_log_three_halves S h Q K hQ hK (fun i _ => hh i) (hcount S))
  simp_rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (hf.sum_le_tsum (Finset.range S.card) (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg hB _))

end Ostmann

end OAI
