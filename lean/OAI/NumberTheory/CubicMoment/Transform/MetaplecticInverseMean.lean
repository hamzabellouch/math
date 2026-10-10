import OAI.NumberTheory.CubicMoment.Transform.MetaplecticActualInverse
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticInverseScale
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedContinuity

namespace OAI

/-! Finite inverse completion transfers actual signed-height means.
The weight norm is estimated pointwise; its height-dependent phase is
retained in the exact identity and never treated as constant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_metaplecticAngularSmoothSum_of_cutoff
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {U B F : ℝ}
    (hU : 0 < U) (hBF : B*U ≤ F) (hW : ∀ x : ℝ, B < x → W x = 0) :
    Continuous (metaplecticAngularSmoothSum r ℓ W U) := by
  have hc : Continuous (fun t : ℝ => ∑ u ∈ primaryElementBall F,
      W (norm u/U)*(gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))) := by
    apply continuous_finsetSum
    intro u _
    unfold mellinPhase
    fun_prop
  exact hc.congr (fun t => (metaplecticAngularSmoothSum_finite r ℓ W hU hBF hW t).symm)

lemma metaplectic_inverse_pointwise_norm
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {U B F : ℝ}
    (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    ‖metaplecticAngularSmoothSum r ℓ W U t‖ ≤
      ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖ := by
  rw [metaplectic_angular_actual_inverse r ℓ W hU hB hBF hW t]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c hc
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_metaplectic_inverse_weight r ℓ t (mem_primaryElementBall.mp hc).1)
    (_root_.norm_nonneg _)

lemma metaplectic_inverse_interval_norm
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    {U B F a b : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (hab : a ≤ b) :
    (∫ t in a..b, ‖metaplecticAngularSmoothSum r ℓ W U t‖) ≤
      ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        (∫ t in a..b, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖) := by
  have hf := (continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ W hU hBF hW).norm
  have hc (c : Eisenstein) (hc : c ∈ primaryElementBall F) :
      Continuous (fun t : ℝ => Real.sqrt (norm c)*
        ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖) := by
    have hcp := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hc).1)
    exact continuous_const.mul
      (continuous_metaplectic_height_completed r ℓ W hWc (div_pos hU (pow_pos hcp 3))).norm
  have hg : Continuous (fun t : ℝ => ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
      ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖) :=
    continuous_finsetSum _ hc
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)
    (fun t _ => metaplectic_inverse_pointwise_norm r ℓ W hU hB hBF hW t)
  apply hi.trans_eq
  rw [intervalIntegral.integral_finsetSum (fun c hc' => (hc c hc').intervalIntegrable a b)]
  simp only [intervalIntegral.integral_const_mul]

/-- The only loss in inverse completion is the actual finite harmonic
norm sum. The completed-mean premise is discharged by the published-input
angular bound in the subsequent application. -/
theorem metaplectic_inverse_signed_mean
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    {U B F T H : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (hT : 0 < T)
    (hmean : ∀ c ∈ primaryElementBall F,
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖))/T ≤
          H*Real.sqrt (U/norm c^3)) :
    ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r ℓ W U t‖)+
      (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r ℓ W U t‖))/T ≤
        H*Real.sqrt U*(∑ c ∈ primaryElementBall F, norm c^(-1:ℝ)) := by
  have hn := metaplectic_inverse_interval_norm r ℓ W hWc hU hB hBF hW
    (show -(2*T) ≤ -T by linarith)
  have hp := metaplectic_inverse_interval_norm r ℓ W hWc hU hB hBF hW
    (show T ≤ 2*T by linarith)
  calc
    _ ≤ ((∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
          (∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖))+
        (∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
          (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖)))/T :=
      div_le_div_of_nonneg_right (add_le_add hn hp) hT.le
    _ = ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        (((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖)+
          (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W (U/norm c^3) t‖))/T) := by
      rw [←Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*(H*Real.sqrt (U/norm c^3)) :=
      Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_left (hmean c hc) (Real.sqrt_nonneg _))
    _ = H*Real.sqrt U*(∑ c ∈ primaryElementBall F, norm c^(-1:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hcp := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hc).1)
      calc
        _ = H*(Real.sqrt (norm c)*Real.sqrt (U/norm c^3)) := by ring
        _ = H*(Real.sqrt U/norm c) := by rw [metaplectic_inverse_sqrt_scale hU.le hcp]
        _ = _ := by rw [Real.rpow_neg_one]; ring

end CubicFirstMoment

end

end OAI
