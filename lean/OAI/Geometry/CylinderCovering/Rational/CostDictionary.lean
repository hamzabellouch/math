import OAI.Geometry.CylinderCovering.Rational.CoordinateDictionary

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RationalDictionary

def labelDerivative : Plane →L[ℝ] Plane :=
  (Matrix.toLpLin 2 2 (!![ell, 0; 0, -(1 / 2 : ℝ)])).toContinuousLinearMap

theorem labelDerivative_apply (p : Plane) :
    labelDerivative p = vec2 (ell * p 0) (-p 1 / 2) := by
  ext i
  fin_cases i <;> simp [labelDerivative, Matrix.toLpLin_apply,
    dotProduct, Fin.sum_univ_two, vec2]
  ring

theorem labelMap_eq_affine (p : Plane) :
    labelMap p = labelDerivative p + vec2 0 (1 / 2) := by
  rw [labelDerivative_apply]
  ext i
  fin_cases i <;> simp [labelMap, vec2]
  ring

theorem labelMap_hasFDerivAt (p : Plane) : HasFDerivAt labelMap labelDerivative p := by
  have he : labelMap = fun x => labelDerivative x + vec2 0 (1 / 2) :=
    funext labelMap_eq_affine
  rw [he]
  exact (labelDerivative.hasFDerivAt (x := p)).add_const (vec2 0 (1 / 2))

theorem labelDerivative_det : labelDerivative.det = -ell / 2 := by
  change LinearMap.det ((Matrix.toLpLin 2 2) (!![ell, 0; 0, -(1 / 2 : ℝ)])) = -ell / 2
  rw [Matrix.toLpLin_eq_toLin, LinearMap.det_toLin]
  simp [Matrix.det_fin_two]
  ring

theorem labelMap_injective : Function.Injective labelMap :=
  Function.LeftInverse.injective inverseLabelMap_labelMap

theorem uncenteredDomain_measurable (d0 eta0 k : ℝ) :
    MeasurableSet (uncenteredDomain d0 eta0 k) := by
  unfold uncenteredDomain a0 A0 B0
  measurability

theorem labelMap_image_domain {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    labelMap '' uncenteredDomain d0 eta0 k =
      SlopeRational.labelDomain (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, rfl⟩
    exact (labelDomain_iff hd eta0 k p).mp hp
  · intro q hq
    refine ⟨inverseLabelMap q, ?_, labelMap_inverseLabelMap q⟩
    apply (labelDomain_iff hd eta0 k (inverseLabelMap q)).mpr
    simpa using hq

theorem cost_dictionary {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    centeredCost (centeredRegularization d0) (centeredTilt d0 k)
      (centeredPadding eta0 k) = uncenteredCost d0 eta0 k / 8 := by
  unfold centeredCost uncenteredCost
  rw [← labelMap_image_domain hd eta0 k]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (uncenteredDomain_measurable d0 eta0 k)
    (fun p _ => (labelMap_hasFDerivAt p).hasFDerivWithinAt)
    labelMap_injective.injOn]
  rw [labelDerivative_det]
  have habs' : |-ell / 2| = ell / 2 := by rw [neg_div, abs_neg, abs_of_pos (div_pos ell_pos (by norm_num))]
  rw [habs']
  calc
    (∫ p in uncenteredDomain d0 eta0 k,
      (ell / 2) • centeredWeight (centeredRegularization d0) (centeredTilt d0 k) (labelMap p)) =
      ∫ p in uncenteredDomain d0 eta0 k, (1 / 8 : ℝ) * uncenteredWeight d0 k p := by
        apply setIntegral_congr_fun (uncenteredDomain_measurable d0 eta0 k)
        intro p hp
        have hs : p 1 + d0 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hp.1 hd)
        unfold centeredWeight uncenteredWeight centeredRegularization labelMap
        simp only [vec2_zero, vec2_one, smul_eq_mul]
        rw [squared_slope_dictionary hs k (p 0)]
        have he : ell / 2 * c0 = 1 / 8 := by nlinarith [ell_mul_c0]
        rw [← mul_div_assoc, he]
        ring
    _ = (∫ p in uncenteredDomain d0 eta0 k, uncenteredWeight d0 k p) / 8 := by
      rw [integral_const_mul]
      ring

theorem uncenteredWeight_eq_norm (d0 k : ℝ) (p : Plane) :
    uncenteredWeight d0 k p = 1 / Real.sqrt (1 + k ^ 2 * ‖velocity d0 p‖ ^ 2) := by
  unfold uncenteredWeight
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [velocity, vec2, Fin.sum_univ_two]

end RationalDictionary

end

end OAI
