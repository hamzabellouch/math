import OAI.Geometry.NodalSets.Elliptic.CorrugationLocalHessian

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugation_fast_hessian_lower {amp B : ℝ} (ha : 0 ≤ amp) (hB : 0 ≤ B)
    (z v : ℝ × ℝ)
    (hb : corrugationCellRadius z ≠ 0 →
      |radialComponent (corrugationCellPoint z) v (corrugationCellRadius z)| ≤ B) :
    -(max (-deriv (corrugationSlope amp (1/4)) (corrugationCellRadius z)) 0 * B^2) ≤
      fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) z v v := by
  by_cases hr : corrugationCellRadius z = 0
  · exact (neg_nonpos.mpr (mul_nonneg (le_max_right _ _) (sq_nonneg B))).trans
      (corrugationPeriodicWell_radius_zero_positive ha z v hr)
  · rw [(corrugationPeriodicWell_global_radial_jets amp z v v hr).2]
    let r := corrugationCellRadius z
    let d := max (-deriv (corrugationSlope amp (1/4)) r) 0
    let u := radialComponent (corrugationCellPoint z) v r
    let t := angularComponent (corrugationCellPoint z) v r
    have hr0 : 0 < r := lt_of_le_of_ne (corrugationCellRadius_properties z).1 (Ne.symm hr)
    have hl : 0 ≤ corrugationSlope amp (1/4) r := corrugationSlope_nonneg ha hr0.le
    have hu : u^2 ≤ B^2 := by
      have h := hb hr
      have hsq := sq_le_sq₀ (abs_nonneg u) hB
      exact (sq_abs u).symm.trans_le (hsq.mpr h)
    have hd : 0 ≤ d := le_max_right _ _
    have hdp : -d ≤ deriv (corrugationSlope amp (1/4)) r := by
      have h := le_max_left (-deriv (corrugationSlope amp (1/4)) r) 0
      dsimp [d]; linarith
    have hq := mul_le_mul_of_nonneg_right hdp (sq_nonneg u)
    have hs := mul_le_mul_of_nonneg_left hu hd
    have ht := mul_nonneg (div_nonneg hl hr0.le) (sq_nonneg t)
    change -(d*B^2) ≤ deriv (corrugationSlope amp (1/4)) r*u*u+
      (corrugationSlope amp (1/4) r/r)*t*t
    nlinarith only [hq,hs,ht]

lemma weighted_hessian_perturbation_lower {ν H₁ H₂ F₁ F₂ E₁ E₂ B E : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hF₁ : -B ≤ F₁) (hF₂ : -B ≤ F₂) (hE₁ : |E₁| ≤ E) (hE₂ : |E₂| ≤ E) :
    ν*H₁+H₂-2*B-2*E ≤ ν*(H₁+F₁+E₁)+(H₂+F₂+E₂) := by
  have h1 := mul_le_mul_of_nonneg_left hF₁ hν0
  have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hE₁).1 hν0
  have h3 := mul_le_mul_of_nonneg_right hν1 hB
  have h4 := mul_le_mul_of_nonneg_right hν1 hE
  have h5 := (abs_le.mp hE₂).1
  nlinarith

end
end Yau.Geometry

end OAI
