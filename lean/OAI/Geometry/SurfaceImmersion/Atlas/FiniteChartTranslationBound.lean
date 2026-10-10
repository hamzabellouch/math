import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartTranslationBound

namespace OAI

/-! Smallness simultaneously in any fixed finite collection of compact
chart regions. The bound is independent of the translated map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [Fintype ι]

def ChartDerivativeClose (p : ι → M) (S : ι → Set Base)
    (f g : M → ProjectionTarget 3) (ε : ℝ) : Prop :=
  ∀ i x, x ∈ S i → ‖fderiv ℝ (g ∘ (chart (p i)).symm) x-
    fderiv ℝ (f ∘ (chart (p i)).symm) x‖ < ε

theorem finite_chart_translation_bound
    (p : ι → M) (S : ι → Set Base) (hS : ∀ i, IsCompact (S i))
    (hST : ∀ i, S i ⊆ (chart (p i)).target) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {f : M → ProjectionTarget 3},
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f →
      ∀ a : ProjectionTarget 3, ‖a‖ < δ →
      ChartDerivativeClose p S f (surfaceTranslation f χ a) ε := by
  classical
  choose δ hδ hb using fun i => compact_chart_translation_bound (p i) hχ (hS i) (hST i) hε
  have hsmall (s : Finset ι) : ∃ η > 0, ∀ i ∈ s, η ≤ δ i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨η,hη,he⟩ := ih
      refine ⟨min η (δ i),lt_min hη (hδ i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (he j hj)
  obtain ⟨η,hη,he⟩ := hsmall Finset.univ
  exact ⟨η,hη,fun hf a ha i x hx => hb i hf a (ha.trans_le (he i (Finset.mem_univ i))) x hx⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
