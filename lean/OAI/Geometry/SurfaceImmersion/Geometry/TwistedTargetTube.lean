import OAI.Geometry.SurfaceImmersion.Whitney.TwistedRuledCoordinates

namespace OAI

/-! A twist stays in the same transverse tube and gives a genuine
 immersed surface after composition with the constructed target tube. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma twistedRuledCoordinates_bound (θ : Base → ℝ) (x : Base) :
    ‖(twistedRuledCoordinates θ x).1‖ ≤ |x 0| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg (x 0))).mpr
  intro i
  fin_cases i
  · change |x 0*Real.cos (θ x)| ≤ |x 0|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  · change |x 0*Real.sin (θ x)| ≤ |x 0|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩)

def twistedTubeSurface (T : Base × ℝ → Fin 3 → ℝ) (θ : Base → ℝ) : Base → ProjectionTarget 3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ∘ T ∘ twistedRuledCoordinates θ

lemma twistedTubeSurface_smooth {T : Base × ℝ → Fin 3 → ℝ} {θ : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (twistedTubeSurface T θ) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp (hT.comp (twistedRuledCoordinates_smooth hθ))

lemma twistedTubeSurface_immersion {T : Base × ℝ → Fin 3 → ℝ} {θ : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hθ : ContDiff ℝ ∞ θ) {x : Base}
    (hI : Function.Injective (fderiv ℝ T (twistedRuledCoordinates θ x))) :
    Function.Injective (fderiv ℝ (twistedTubeSurface T θ) x) := by
  rw [twistedTubeSurface,fderiv_comp x
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiableAt
    ((hT.comp (twistedRuledCoordinates_smooth hθ)).differentiable (by simp) x),
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.fderiv,
    fderiv_comp x (hT.differentiable (by simp) _)
      ((twistedRuledCoordinates_smooth hθ).differentiable (by simp) x)]
  intro v w hvw
  apply twistedRuledCoordinates_immersion hθ x
  apply hI
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.injective hvw

lemma twistedTubeSurface_eq_zero {T : Base × ℝ → Fin 3 → ℝ} {θ : Base → ℝ}
    {x : Base} (hx : θ x = 0) : twistedTubeSurface T θ x = twistedTubeSurface T 0 x := by
  simp only [twistedTubeSurface,Function.comp_apply,twistedRuledCoordinates_zero hx]
  rw [twistedRuledCoordinates_zero (show (0 : Base → ℝ) x = 0 from rfl)]

lemma twistedTubeSurface_difference_support (T : Base × ℝ → Fin 3 → ℝ) (θ : Base → ℝ) :
    tsupport (twistedTubeSurface T θ-twistedTubeSurface T 0) ⊆ tsupport θ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_tsupport
  intro hz
  apply hx
  exact sub_eq_zero.mpr (twistedTubeSurface_eq_zero hz)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
