import OAI.Geometry.SurfaceImmersion.Whitney.SmoothSurfaceDoubleChart

namespace OAI

/-! At two regular sheets the smooth paired double curve projects to
regular curves on both sheets.  Equal image velocities supply the key relation. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma equal_image_curve_derivatives {f : M → ProjectionTarget 3} {A B : ℝ → M} {t : ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ A t)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ B t)
    (heq : f ∘ A =ᶠ[𝓝 t] f ∘ B) :
    (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)).comp
        (mfderiv 𝓘(ℝ) planeModel A t) =
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)).comp
        (mfderiv 𝓘(ℝ) planeModel B t) := by
  have he := heq.mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ,ProjectionTarget 3))
  rw [mfderiv_comp t (hf.mdifferentiable (by simp)).mdifferentiableAt
    (hA.mdifferentiableAt (by simp)),
    mfderiv_comp t (hf.mdifferentiable (by simp)).mdifferentiableAt
    (hB.mdifferentiableAt (by simp))] at he
  exact he

lemma paired_injective_of_equal_images
    {W : Type*} {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : W →L[ℝ] E) (B : W →L[ℝ] F) (P : E →L[ℝ] G) (Q : F →L[ℝ] G)
    (hpair : Function.Injective (A.prod B))
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (heq : P.comp A = Q.comp B) : Function.Injective A ∧ Function.Injective B := by
  constructor
  · intro u v huv
    apply hpair
    apply Prod.ext huv
    change B u = B v
    apply hQ
    have hh := congrArg P huv
    change (P.comp A) u = (P.comp A) v at hh
    simpa only [heq,ContinuousLinearMap.comp_apply] using hh
  · intro u v huv
    apply hpair
    apply Prod.ext _ huv
    change A u = A v
    apply hP
    have hh := congrArg Q huv
    change (Q.comp B) u = (Q.comp B) v at hh
    simpa only [← heq,ContinuousLinearMap.comp_apply] using hh

theorem regular_double_curve_velocities {f : M → ProjectionTarget 3}
    {A B : ℝ → M} {t : ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ A t)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ B t)
    (heq : f ∘ A =ᶠ[𝓝 t] f ∘ B)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel A t).prod (mfderiv 𝓘(ℝ) planeModel B t)))
    (hAf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)))
    (hBf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t))) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel A t) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel B t) :=
by
  have hrel := equal_image_curve_derivatives hf hA hB heq
  constructor
  · intro u v huv
    apply hpair
    apply Prod.ext huv
    change mfderiv 𝓘(ℝ) planeModel B t u = mfderiv 𝓘(ℝ) planeModel B t v
    apply hBf
    have hh := congrArg (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)) huv
    change ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)).comp
      (mfderiv 𝓘(ℝ) planeModel A t)) u =
      ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A t)).comp
      (mfderiv 𝓘(ℝ) planeModel A t)) v at hh
    rw [hrel] at hh
    exact hh
  · intro u v huv
    apply hpair
    apply Prod.ext _ huv
    change mfderiv 𝓘(ℝ) planeModel A t u = mfderiv 𝓘(ℝ) planeModel A t v
    apply hAf
    have hh := congrArg (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)) huv
    change ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)).comp
      (mfderiv 𝓘(ℝ) planeModel B t)) u =
      ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B t)).comp
      (mfderiv 𝓘(ℝ) planeModel B t)) v at hh
    rw [← hrel] at hh
    exact hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
