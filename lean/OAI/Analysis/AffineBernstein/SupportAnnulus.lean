import Mathlib
import OAI.Analysis.AffineBernstein.SupportArea
import OAI.Analysis.AffineBernstein.MatrixShiftBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {n : ℕ}

lemma toMatrix_fderiv_gradient_eq_hessian_transpose {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ (gradient u) x).toLinearMap =
      (hessian u x).transpose := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (OrthonormalBasis.repr (EuclideanSpace.basisFun (Fin n) ℝ)
    (fderiv ℝ (gradient u) x ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i = _
  rw [OrthonormalBasis.repr_apply_apply,real_inner_comm,
    inner_fderiv_gradient hu,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_apply]
  exact (hessian_eq_second hu j i).symm

lemma det_fderiv_shiftedGradient {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    (fderiv ℝ (fun x => gradient u x + x) x).det = (hessian u x + 1).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he : (fderiv ℝ (fun x => gradient u x + x) x).toLinearMap =
      (fderiv ℝ (gradient u) x).toLinearMap + LinearMap.id := by
    change (fderiv ℝ (fun y => gradient u y + id y) x).toLinearMap = _
    rw [fderiv_fun_add ((contDiffAt_gradient hu).differentiableAt (by simp)) differentiableAt_id,
      fderiv_id]
    rfl
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,he,map_add,
    toMatrix_fderiv_gradient_eq_hessian_transpose hu,LinearMap.toMatrix_id]
  have ht : (hessian u x).transpose + (1 : Matrix (Fin n) (Fin n) ℝ) =
      (hessian u x + 1).transpose := by
    ext i j
    simp only [Matrix.add_apply,Matrix.transpose_apply,Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij,Ne.symm]
  rw [ht,Matrix.det_transpose]

/- On any bounded measurable annular set, the cofactor trace of the literal
support Hessian has a bound depending only on the radius of the convex fiber.
The proof uses the injective shifted Gauss map and genuine change of variables. -/
lemma lintegral_support_cofactor_le_ball {K D : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) (hD : MeasurableSet D)
    (hH : ∀ x ∈ D, ContDiffAt ℝ ∞ (homogeneousSupport K) x)
    {R r : ℝ} (hR : ∀ y ∈ K, ‖y‖ ≤ R) (hr : ∀ x ∈ D, ‖x‖ ≤ r) :
    (∫⁻ x in D, ENNReal.ofReal (hessian (homogeneousSupport K) x).adjugate.trace) ≤
      (n : ℝ≥0∞) * volume (Metric.closedBall (0 : Space n) (R+r)) := by
  let G := fun x => gradient (homogeneousSupport K) x + x
  have hd (x : Space n) (hx : x ∈ D) : DifferentiableAt ℝ G x :=
    ((contDiffAt_gradient (hH x hx)).differentiableAt (by simp)).add differentiableAt_id
  have hi : Set.InjOn G D := shiftedGauss_injOn hK hne
    (fun x hx => (hH x hx).differentiableAt (by simp))
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) hi (fun _ : Space n => (1:ℝ≥0∞))
  simp only [lintegral_const,Measure.restrict_apply_univ,mul_one,one_mul] at hj
  have hm : G '' D ⊆ Metric.closedBall 0 (R+r) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add
      (hR _ (gaussPoint_mem_support hK hne ((hH x hx).differentiableAt (by simp))).1) (hr x hx))
  calc
    _ ≤ ∫⁻ x in D, (n:ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ G x).det| := by
      apply setLIntegral_mono' hD
      intro x hx
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      apply ENNReal.ofReal_le_ofReal
      have hp := homogeneousSupport_hessian_posSemidef hK hne (hH x hx)
      have hdpos : 0 ≤ (hessian (homogeneousSupport K) x + 1).det :=
        (hp.add Matrix.PosSemidef.one).det_nonneg
      rw [show G = (fun x => gradient (homogeneousSupport K) x + x) from rfl,
        det_fderiv_shiftedGradient (hH x hx),abs_of_nonneg hdpos]
      simpa using trace_adjugate_le_card_mul_det_add_one hp
    _ = (n:ℝ≥0∞) * ∫⁻ x in D, ENNReal.ofReal |(fderiv ℝ G x).det| := by
      rw [lintegral_const_mul']
      exact ENNReal.natCast_ne_top n
    _ ≤ _ := by rw [← hj]; exact mul_le_mul_right (measure_mono (μ := volume) hm) _

end AffineBernstein
end

end OAI
