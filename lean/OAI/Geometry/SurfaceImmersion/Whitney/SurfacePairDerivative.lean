import OAI.Geometry.SurfaceImmersion.Atlas.ChartGermImmersion
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceGermTranslation

namespace OAI

/-! Intrinsic double-point transversality and its actual coordinate
representatives. The derivative is defined on the two tangent planes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfacePairDerivative (f : M → ProjectionTarget 3) (x y : M) :
    (TangentSpace planeModel x × TangentSpace planeModel y) →L[ℝ] ProjectionTarget 3 :=
  (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x).comp (ContinuousLinearMap.fst ℝ _ _) -
    (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f y).comp (ContinuousLinearMap.snd ℝ _ _)

lemma chart_germ_mfderiv (p : M) {x : M} (hx : x ∈ (chart p).source)
    {f : M → ProjectionTarget 3} {F : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (he : f =ᶠ[𝓝 x] F ∘ chart p) :
    (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x :
      TangentSpace planeModel x →L[ℝ] ProjectionTarget 3) =
      (fderiv ℝ F (chart p x)).comp (mfderiv planeModel 𝓘(ℝ,Base) (chart p) x) := by
  have hFc : ContMDiff 𝓘(ℝ,Base) 𝓘(ℝ,ProjectionTarget 3) ∞ F := hF.contMDiff
  apply ContinuousLinearMap.ext
  intro v
  rw [he.mfderiv_eq,mfderiv_comp x (hFc.mdifferentiable (by simp)).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt hx),mfderiv_eq_fderiv]
  rfl

theorem surface_pair_coordinate_regular_iff (p q : M) {x y : M}
    (hx : x ∈ (chart p).source) (hy : y ∈ (chart q).source)
    {f : M → ProjectionTarget 3} {F G : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (heF : f =ᶠ[𝓝 x] F ∘ chart p) (heG : f =ᶠ[𝓝 y] G ∘ chart q) :
    Function.Surjective (surfacePairDerivative f x y) ↔
      Function.Surjective (fderiv ℝ (fun z : Base × Base => F z.1-G z.2)
        (chart p x,chart q y)) := by
  let C₁ : TangentSpace planeModel x →L[ℝ] Base := mfderiv planeModel 𝓘(ℝ,Base) (chart p) x
  let C₂ : TangentSpace planeModel y →L[ℝ] Base := mfderiv planeModel 𝓘(ℝ,Base) (chart q) y
  let C : (TangentSpace planeModel x × TangentSpace planeModel y) →L[ℝ] (Base × Base) := C₁.prodMap C₂
  have hC : Function.Surjective C := by
    rintro ⟨a,b⟩
    obtain ⟨v,hv⟩ := (chart_mdifferentiable p).mfderiv_surjective hx a
    obtain ⟨w,hw⟩ := (chart_mdifferentiable q).mfderiv_surjective hy b
    exact ⟨(v,w),Prod.ext hv hw⟩
  have hd := (((hF.differentiable (by simp) (chart p x)).hasFDerivAt.comp
      (chart p x,chart q y) ((ContinuousLinearMap.fst ℝ Base Base).hasFDerivAt)).sub
    ((hG.differentiable (by simp) (chart q y)).hasFDerivAt.comp
      (chart p x,chart q y) ((ContinuousLinearMap.snd ℝ Base Base).hasFDerivAt))).fderiv
  change fderiv ℝ (fun z : Base × Base => F z.1-G z.2) (chart p x,chart q y) = _ at hd
  have he : surfacePairDerivative f x y =
      (fderiv ℝ (fun z : Base × Base => F z.1-G z.2) (chart p x,chart q y)).comp C := by
    rw [hd]
    apply ContinuousLinearMap.ext
    intro v
    simp only [surfacePairDerivative,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    rw [chart_germ_mfderiv p hx hF heF,chart_germ_mfderiv q hy hG heG]
    rfl
  rw [he]
  constructor
  · intro h z
    obtain ⟨v,hv⟩ := h z
    exact ⟨C v,hv⟩
  · exact fun h => h.comp hC

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
