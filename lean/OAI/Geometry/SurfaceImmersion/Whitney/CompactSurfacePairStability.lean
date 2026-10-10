import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartPairStability
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartRepresentative

namespace OAI

/-! Compact stability of actual surface double-point transversality
under a fixed smooth scalar-weighted translation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem compact_surface_pair_stability
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    {K : Set (M × M)} (hK : IsCompact K)
    (hreg : ∀ z ∈ K, f z.1 = f z.2 → Function.Surjective (surfacePairDerivative f z.1 z.2)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      surfaceTranslation f χ a z.1 = surfaceTranslation f χ a z.2 →
      Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) z.1 z.2) := by
  classical
  have hlocal (z : K) : ∃ (W : Set (M × M)) (δ : ℝ), IsOpen W ∧ (z : M × M) ∈ W ∧
      0 < δ ∧ ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ w ∈ K ∩ W,
      surfaceTranslation f χ a w.1 = surfaceTranslation f χ a w.2 →
      Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) w.1 w.2) := by
    obtain ⟨U₁,F,hU₁,hxU₁,hU₁s,hF,heF⟩ := surface_chart_representative hf z.val.1
    obtain ⟨U₂,ρ,hU₂,hxU₂,hU₂s,hρ,heρ⟩ := scalar_surface_chart_representative hχ z.val.1
    obtain ⟨V₁,G,hV₁,hyV₁,hV₁s,hG,heG⟩ := surface_chart_representative hf z.val.2
    obtain ⟨V₂,σ,hV₂,hyV₂,hV₂s,hσ,heσ⟩ := scalar_surface_chart_representative hχ z.val.2
    let U := U₁ ∩ U₂
    let V := V₁ ∩ V₂
    have hU : IsOpen U := hU₁.inter hU₂
    have hV : IsOpen V := hV₁.inter hV₂
    obtain ⟨T,hT,hzT,hTUV⟩ := exists_compact_subset (hU.prod hV) ⟨⟨hxU₁,hxU₂⟩,hyV₁,hyV₂⟩
    have hKT : IsCompact (K ∩ T) := hK.inter hT
    obtain ⟨δ,hδ,hδreg⟩ := surface_chart_pair_stability z.val.1 z.val.2 hF hG hρ hσ hU hV
      (fun x hx => hU₁s hx.1) (fun x hx => hV₁s hx.1)
      (heF.mono inter_subset_left) (heG.mono inter_subset_left)
      (heρ.mono inter_subset_right) (heσ.mono inter_subset_right)
      hKT (fun _ hx => hTUV hx.2) (fun w hw => hreg w hw.1)
    refine ⟨interior T,δ,isOpen_interior,hzT,hδ,?_⟩
    intro a ha w hw
    exact hδreg a ha w ⟨hw.1,interior_subset hw.2⟩
  choose W δ hW hzW hδ hδreg using hlocal
  have hcover : K ⊆ ⋃ z : K, W z := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzW ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover W hW hcover
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
  intro a ha z hz
  obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hs hz)
  exact hδreg i a (ha.trans_le (hεs i hi)) z ⟨hz,hzi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
