import OAI.Geometry.SurfaceImmersion.Geometry.CompactTranslationImmersion
import OAI.Geometry.SurfaceImmersion.Whitney.CompactSurfacePairStability

namespace OAI

/-! Immersion on a compact part of the surface is preserved by small
parameters in a fixed smooth scalar translation family. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem compact_surface_immersion_stability
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    {K : Set M} (hK : IsCompact K)
    (hI : ∀ x ∈ K, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ K,
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (surfaceTranslation f χ a) x) := by
  classical
  have hlocal (z : K) : ∃ (V : Set M) (δ : ℝ), IsOpen V ∧ (z : M) ∈ V ∧
      0 < δ ∧ ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ K ∩ V,
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (surfaceTranslation f χ a) x) := by
    obtain ⟨U₁,F,hU₁,hzU₁,hU₁s,hF,heF⟩ := surface_chart_representative hf z.val
    obtain ⟨U₂,ρ,hU₂,hzU₂,hU₂s,hρ,heρ⟩ := scalar_surface_chart_representative hχ z.val
    let U := U₁ ∩ U₂
    have hU : IsOpen U := hU₁.inter hU₂
    obtain ⟨T,hT,hzT,hTU⟩ := exists_compact_subset hU ⟨hzU₁,hzU₂⟩
    have hKT : IsCompact (K ∩ T) := hK.inter hT
    have hs : K ∩ T ⊆ (chart z.val).source := fun x hx => hU₁s (hTU hx.2).1
    have hKc : IsCompact ((chart z.val) '' (K ∩ T)) :=
      hKT.image_of_continuousOn ((chart z.val).continuousOn.mono hs)
    have hIc : ∀ y ∈ (chart z.val) '' (K ∩ T), Function.Injective (fderiv ℝ F y) := by
      rintro y ⟨x,hx,rfl⟩
      exact (chart_germ_immersion_iff z.val (hs hx) hF
        (heF.eventuallyEq_of_mem (hU₁.mem_nhds (hTU hx.2).1))).mp (hI x hx.1)
    obtain ⟨δ,hδ,hstable⟩ := compact_translation_immersion hF hρ hKc hIc
    refine ⟨interior T,δ,isOpen_interior,hzT,hδ,?_⟩
    intro a ha x hx
    have hxT := interior_subset hx.2
    have hxU := hTU hxT
    apply (chart_germ_immersion_iff z.val (hU₁s hxU.1) (hF.add (hρ.smul contDiff_const))
      (surface_translation_chart_germ z.val
        (heF.eventuallyEq_of_mem (hU₁.mem_nhds hxU.1))
        (heρ.eventuallyEq_of_mem (hU₂.mem_nhds hxU.2)) a)).mpr
    exact hstable a ha (chart z.val x) ⟨x,⟨hx.1,hxT⟩,rfl⟩
  choose V δ hV hzV hδ hδI using hlocal
  have hcover : K ⊆ ⋃ z : K, V z := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzV ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV hcover
  have hsmall : ∃ ε > 0, ∀ i ∈ s, ε ≤ δ i := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε,hε,hεs⟩ := ih
      refine ⟨min ε (δ i),lt_min hε (hδ i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεs j hj)
  obtain ⟨ε,hε,hεs⟩ := hsmall
  refine ⟨ε,hε,?_⟩
  intro a ha x hx
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
  exact hδI i a (ha.trans_le (hεs i hi)) x ⟨hx,hxi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
