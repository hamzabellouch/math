import OAI.NumberTheory.CubicMoment.Transform.MetaplecticInverseMean
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortResidue

namespace OAI

/-! Inverse completion preserves the radial pole error. Its cube-divisor
weight is the absolutely summable inverse square norm. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_inverse_signed_mean_with_pole
    (r : Eisenstein) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    {U B F T H J : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (hT : 0 < T)
    (hmean : ∀ c ∈ primaryElementBall F,
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖))/T ≤
          H*Real.sqrt (U/norm c^3)+J*(U/norm c^3)^(5/6:ℝ)) :
    ((∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r 0 W U t‖)+
      (∫ t in T..2*T, ‖metaplecticAngularSmoothSum r 0 W U t‖))/T ≤
        H*Real.sqrt U*(∑ c ∈ primaryElementBall F, norm c^(-1:ℝ))+
          J*U^(5/6:ℝ)*(∑ c ∈ primaryElementBall F, norm c^(-2:ℝ)) := by
  have hn := metaplectic_inverse_interval_norm r 0 W hWc hU hB hBF hW
    (show -(2*T) ≤ -T by linarith)
  have hp := metaplectic_inverse_interval_norm r 0 W hWc hU hB hBF hW
    (show T ≤ 2*T by linarith)
  calc
    _ ≤ ((∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
          (∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖))+
        (∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
          (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖)))/T :=
      div_le_div_of_nonneg_right (add_le_add hn hp) hT.le
    _ = ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        (((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖)+
          (∫ t in T..2*T, ‖metaplecticHeightCompleted r 0 W (U/norm c^3) t‖))/T) := by
      rw [←Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c ∈ primaryElementBall F, Real.sqrt (norm c)*
        (H*Real.sqrt (U/norm c^3)+J*(U/norm c^3)^(5/6:ℝ)) :=
      Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_left (hmean c hc) (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      have hcp := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hc).1)
      calc
        _ = H*(Real.sqrt (norm c)*Real.sqrt (U/norm c^3))+
            J*(Real.sqrt (norm c)*(U/norm c^3)^(5/6:ℝ)) := by ring
        _ = _ := by
          rw [metaplectic_inverse_sqrt_scale hU.le hcp,
            metaplectic_inverse_residue_scale hU hcp,Real.rpow_neg_one]
          ring

lemma primary_inverse_square_sum_bound (F : ℝ) :
    (∑ c ∈ primaryElementBall F, norm c^(-2:ℝ)) ≤
      ∑' c : Eisenstein, norm c^(-2:ℝ) :=
  (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 2)).sum_le_tsum _
    (fun c _ => Real.rpow_nonneg (norm_nonneg c) _)

end CubicFirstMoment

end

end OAI
