import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFamilies

namespace OAI

/-! Chain rule for substituting a fast linear phase in a smooth periodic family. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Family

def fastValue (U : Family A E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) (p : A) : E :=
  U.val p ((ℓ p / z : ℝ) : Period)

lemma fastValue_smooth (U : Family A E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) :
    ContDiff ℝ ∞ (U.fastValue ℓ z) :=
  U.smooth.comp (contDiff_id.prodMk (ℓ.contDiff.div_const z))

/-- Both slow and angular terms in the derivative of fast evaluation. -/
lemma fastValue_fderiv (U : Family A E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) (p v : A) :
    fderiv ℝ (U.fastValue ℓ z) p v =
      (U.slow v).val p ((ℓ p / z : ℝ) : Period) +
        (ℓ v / z) • U.angle.val p ((ℓ p / z : ℝ) : Period) := by
  let T : A →L[ℝ] A × ℝ := (ContinuousLinearMap.id ℝ A).prod (z⁻¹ • ℓ)
  have hT (p : A) : T p = (p, ℓ p / z) := by
    simp [T, div_eq_mul_inv, mul_comm]
  have hEq : U.fastValue ℓ z =
      (fun w : A × ℝ => U.val w.1 (w.2 : Period)) ∘ T := by
    funext p
    simp only [Function.comp_apply, hT, fastValue]
  rw [hEq, fderiv_comp p (U.smooth.differentiable (by simp) (T p)) T.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, hT]
  change fderiv ℝ (fun w : A × ℝ => U.val w.1 (w.2 : Period)) (p, ℓ p / z) (v, ℓ v / z) = _
  have hv : (v, ℓ v / z) = (v, 0) + (ℓ v / z) • ((0 : A), (1 : ℝ)) := by
    simp
  rw [hv, map_add, map_smul]
  rfl

end Family
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
