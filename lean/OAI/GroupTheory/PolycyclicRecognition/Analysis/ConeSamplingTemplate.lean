import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeFacetTemplate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightSamplingPolytope

namespace OAI

/-! # Compact cone templates inside the actual sampling polytope -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- A fixed positive polar radius works for every sufficiently small
chart enlargement. The translated template lies in the scaled interior
of the actual finite weight polytope. -/
theorem exists_cone_sampling_template
    {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α : I → W →L[ℝ] ℝ) (hne : ∀ i, α i ≠ 0)
    (i₀ : I) (C : ProperCone ℝ (W →L[ℝ] ℝ)) (hC : α i₀ ∈ C)
    {c c' : ℝ} (hc : 0 ≤ c) (hcc : c < c') :
    ∃ (p : W) (ε₀ δ₀ : ℝ), α i₀ p = ‖α i₀‖ ∧
      0 < ε₀ ∧ 0 < δ₀ ∧
      IsCompact ((fun z : W => ε₀ • z) '' conePolarTemplate C) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        (fun z : W => (1 - c' * δ) • p + ε₀ • z) '' conePolarTemplate C ⊆
          (fun y : W => (1 - c * δ) • y) '' interior (weightSamplingPolytope α) := by
  obtain ⟨p, ε₀, δ₀, hp, hε, hδ, hinside⟩ :=
    exists_polar_template_facet_slack α hne i₀ C hC hc hcc
  let δ₁ := min δ₀ (1 / (2 * (c + 1)))
  have hδ₁ : 0 < δ₁ := lt_min hδ (by positivity)
  refine ⟨p, ε₀, δ₁, hp, hε, hδ₁,
    (isCompact_conePolarTemplate C).image (continuous_const.smul continuous_id), ?_⟩
  intro δ hd hδmax x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hbound : δ ≤ 1 / (2 * (c + 1)) := hδmax.trans (min_le_right _ _)
  have hδmax' : δ ≤ δ₀ := hδmax.trans (min_le_left _ _)
  have hstrict := hinside δ hd hδmax' ε₀ hε.le le_rfl z hz
  have hfactor : 0 < 1 - c * δ := by
    have hh := (le_div_iff₀ (show 0 < 2 * (c + 1) by positivity)).mp hbound
    nlinarith
  exact mem_smul_weightSamplingInterior α hfactor _ hstrict

end PolycyclicRecognition

end

end OAI
