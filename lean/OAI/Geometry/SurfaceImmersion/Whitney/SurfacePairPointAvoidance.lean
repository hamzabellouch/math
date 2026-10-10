import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartRepresentative
import OAI.Geometry.SurfaceImmersion.Geometry.FinitePointPairAvoidance

namespace OAI

/-! Actual chart translations can avoid prescribed finite surface points while
retaining transversality at all remaining coincidences. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_pair_patch_translation_avoiding_points (p q : M)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F G : Base → ProjectionTarget 3} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hUp : U ⊆ (chart p).source) (hVq : V ⊆ (chart q).source)
    (heF : EqOn f (F ∘ chart p) U) (heG : EqOn f (G ∘ chart q) V)
    (hχU : EqOn χ 1 U) (hχV : EqOn χ 0 V)
    (S T : Set M) (hS : S.Finite) (hT : T.Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧ ∀ x ∈ U, ∀ y ∈ V,
      surfaceTranslation f χ a x = surfaceTranslation f χ a y →
      x ∉ S ∧ y ∉ T ∧ Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) x y) := by
  obtain ⟨a,ha,hreg⟩ := exists_small_transverse_translation_avoiding_points hF hG
    ((chart p) '' U) ((chart q) '' V)
    ((chart p).isOpen_image_of_subset_source hU hUp)
    ((chart q).isOpen_image_of_subset_source hV hVq)
    ((chart p) '' S) ((chart q) '' T) (hS.image _) (hT.image _) hε
  refine ⟨a,ha,?_⟩
  intro x hx y hy hxy
  have he₁ : surfaceTranslation f χ a =ᶠ[𝓝 x] (fun z => F z+a) ∘ chart p := by
    filter_upwards [hU.mem_nhds hx] with z hz
    simp only [surfaceTranslation,hχU hz,Pi.one_apply,one_smul,Function.comp_apply,heF hz]
  have he₂ : surfaceTranslation f χ a =ᶠ[𝓝 y] G ∘ chart q := by
    filter_upwards [hV.mem_nhds hy] with z hz
    simp only [surfaceTranslation,hχV hz,Pi.zero_apply,zero_smul,add_zero,heG hz]
  have hval : F (chart p x)+a = G (chart q y) := by
    exact he₁.self_of_nhds.symm.trans (hxy.trans he₂.self_of_nhds)
  obtain ⟨hxS,hyT,ht⟩ := hreg (chart p x) ⟨x,hx,rfl⟩ (chart q y) ⟨y,hy,rfl⟩ hval
  refine ⟨(fun h => hxS ⟨x,h,rfl⟩),(fun h => hyT ⟨y,h,rfl⟩),?_⟩
  apply (surface_pair_coordinate_regular_iff p q (hUp hx) (hVq hy)
    (hF.add contDiff_const) hG he₁ he₂).mpr
  have heq : (fun z : Base × Base => (F z.1+a)-G z.2) =
      (fun z : Base × Base => (F z.1-G z.2)+a) := by
    funext z
    abel
  change Function.Surjective (fderiv ℝ (fun z : Base × Base => (F z.1+a)-G z.2) _)
  rw [heq,fderiv_add_const]
  exact ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
