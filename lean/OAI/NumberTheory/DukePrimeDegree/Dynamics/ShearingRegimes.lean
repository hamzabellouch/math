import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingKappa

namespace OAI

/-!
# The two exponential shearing regimes

Over the logarithmic window, the inverse shearing scale is either fixed
or decreases exponentially. Clamping the moving coefficient below its
inactive threshold gives a single logarithmic parameter in `[4*T,5*T]`,
including when the original moving coefficient vanishes.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree

lemma max_fixed_moving_clamp (A U T τ : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hτ : τ ∈ Icc 0 T) :
    max A (Real.exp τ * U) =
      max (max A U) (Real.exp τ * max U (max A U * Real.exp (-T))) := by
  let κ := max A U
  have he : 1 ≤ Real.exp τ := Real.one_le_exp_iff.mpr hτ.1
  have hκ : 0 ≤ κ := hA.trans (le_max_left _ _)
  have hκle : κ ≤ max A (Real.exp τ * U) := by
    apply max_le (le_max_left _ _)
    exact (by nlinarith : U ≤ Real.exp τ * U).trans (le_max_right _ _)
  have hscaled : Real.exp τ * (κ * Real.exp (-T)) ≤ κ := by
    have he' : Real.exp (τ - T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hτ.2])
    calc
      Real.exp τ * (κ * Real.exp (-T)) = κ * Real.exp (τ - T) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ κ := by nlinarith [Real.exp_pos (τ - T)]
  apply le_antisymm
  · apply max_le
    · exact (le_max_left A U).trans (le_max_left _ _)
    · exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos τ).le).trans
        (le_max_right _ _)
  · apply max_le hκle
    rw [mul_max_of_nonneg _ _ (Real.exp_pos τ).le]
    exact max_le (le_max_right _ _) (hscaled.trans hκle)

theorem exists_two_exponential_shearing_regimes
    (A U T : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U) (hT : 0 ≤ T)
    (hnorm : max A U = Real.exp (-4 * T)) :
    ∃ θ : ℝ, 4 * T ≤ θ ∧ θ ≤ 5 * T ∧ ∀ τ ∈ Icc 0 T,
      (max A (Real.exp τ * U))⁻¹ = Real.exp (4 * T) ∨
      (max A (Real.exp τ * U))⁻¹ = Real.exp (θ - τ) := by
  let κ := Real.exp (-4 * T)
  let v := max U (κ * Real.exp (-T))
  have hκ : 0 < κ := Real.exp_pos _
  have hv : 0 < v := (mul_pos hκ (Real.exp_pos _)).trans_le (le_max_right _ _)
  have hvle : v ≤ κ := by
    apply max_le
    · exact (le_max_right A U).trans_eq hnorm
    · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
      nlinarith [Real.exp_pos (-T)]
  have hvlo : Real.exp (-5 * T) ≤ v := by
    have he : κ * Real.exp (-T) = Real.exp (-5 * T) := by
      dsimp only [κ]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← he]
    exact le_max_right _ _
  let θ := -Real.log v
  have hθlo : 4 * T ≤ θ := by
    have h := Real.log_le_log hv hvle
    change Real.log v ≤ Real.log (Real.exp (-4 * T)) at h
    rw [Real.log_exp] at h
    dsimp [θ]
    linarith
  have hθhi : θ ≤ 5 * T := by
    have h := Real.log_le_log (Real.exp_pos (-5 * T)) hvlo
    rw [Real.log_exp] at h
    dsimp [θ]
    linarith
  refine ⟨θ, hθlo, hθhi, ?_⟩
  intro τ hτ
  have heq := max_fixed_moving_clamp A U T τ hA hU hτ
  rw [hnorm] at heq
  change max A (Real.exp τ * U) = max κ (Real.exp τ * v) at heq
  rw [heq]
  by_cases h : Real.exp τ * v ≤ κ
  · left
    rw [max_eq_left h]
    change (Real.exp (-4 * T))⁻¹ = Real.exp (4 * T)
    rw [← Real.exp_neg]
    congr 1
    ring
  · right
    rw [max_eq_right (le_of_not_ge h)]
    simp [θ, Real.exp_sub, Real.exp_neg, Real.exp_log hv, div_eq_mul_inv, mul_inv_rev]

end DukePrimeDegree

end

end OAI
