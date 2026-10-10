import OAI.Geometry.SurfaceImmersion.Geometry.ClosedFamilySeparator
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceCompactRepresentative
import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairPatchTranslation

namespace OAI

/-! Pair patches and their cutoffs are fixed before the surface map or
perturbation size. Whole closed crosscap neighborhoods may be frozen. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

structure SurfacePairTranslationPatch (p q : M) where
  χ : M → ℝ
  smooth : ContMDiff planeModel 𝓘(ℝ) ∞ χ
  bounds : ∀ x, χ x ∈ Icc 0 1
  U : Set M
  V : Set M
  openU : IsOpen U
  openV : IsOpen V
  memU : p ∈ U
  memV : q ∈ V
  sourceU : closure U ⊆ (chart p).source
  sourceV : closure V ⊆ (chart q).source
  oneOn : EqOn χ 1 U
  zeroOn : EqOn χ 0 V

theorem exists_fixed_surface_pair_patch {ι : Type*} [Fintype ι]
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (p q : M) (hpq : p ≠ q) (hpair : ∀ i, ¬ (p ∈ A i ∧ q ∈ A i)) :
    ∃ P : SurfacePairTranslationPatch p q, ∀ i,
      (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
  obtain ⟨χ,hχ,hχbounds,hpχ,hqχ,hAχ⟩ := closed_family_separator A hA hdis p q hpq hpair
  obtain ⟨Wp,hχWp,hWp,hpWp⟩ := _root_.mem_nhds_iff.mp hpχ
  obtain ⟨Wq,hχWq,hWq,hqWq⟩ := _root_.mem_nhds_iff.mp hqχ
  have hpS : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have hqS : q ∈ (chart q).source := by simpa only [chart_source] using mem_chart_source Plane q
  have hpO : ({p} : Set M) ⊆ Wp ∩ (chart p).source := singleton_subset_iff.mpr ⟨hpWp,hpS⟩
  have hqO : ({q} : Set M) ⊆ Wq ∩ (chart q).source := singleton_subset_iff.mpr ⟨hqWq,hqS⟩
  obtain ⟨U,hU,hpU,hclU⟩ := (isCompact_singleton (x := p)).exists_isOpen_closure_subset
    ((hWp.inter (chart p).open_source).mem_nhdsSet.mpr hpO)
  obtain ⟨V,hV,hqV,hclV⟩ := (isCompact_singleton (x := q)).exists_isOpen_closure_subset
    ((hWq.inter (chart q).open_source).mem_nhdsSet.mpr hqO)
  refine ⟨{
    χ := χ
    smooth := hχ
    bounds := hχbounds
    U := U
    V := V
    openU := hU
    openV := hV
    memU := hpU (mem_singleton p)
    memV := hqV (mem_singleton q)
    sourceU := fun x hx => (hclU hx).2
    sourceV := fun x hx => (hclV hx).2
    oneOn := fun x hx => hχWp ((hclU (subset_closure hx)).1)
    zeroOn := fun x hx => hχWq ((hclV (subset_closure hx)).1)
  },hAχ⟩

namespace SurfacePairTranslationPatch

omit [T2Space M] in
theorem regularize {p q : M} (P : SurfacePairTranslationPatch p q)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧ ∀ x ∈ P.U, ∀ y ∈ P.V,
      surfaceTranslation f P.χ a x = surfaceTranslation f P.χ a y →
      Function.Surjective (surfacePairDerivative (surfaceTranslation f P.χ a) x y) := by
  obtain ⟨F,hF,heF⟩ := surface_compact_representative hf p isClosed_closure.isCompact P.sourceU
  obtain ⟨G,hG,heG⟩ := surface_compact_representative hf q isClosed_closure.isCompact P.sourceV
  exact surface_pair_patch_translation p q hF hG P.openU P.openV
    (fun x hx => P.sourceU (subset_closure hx)) (fun y hy => P.sourceV (subset_closure hy))
    (heF.mono subset_closure) (heG.mono subset_closure) P.oneOn P.zeroOn hε

end SurfacePairTranslationPatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
