import OAI.Analysis.CoulombTransport.CoulombEstimates
import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.FirstCoordinateLift

open CoulombEstimates

/-- Replacing only the first coordinate by a nearby point preserves half the
separation, without any component-label hypothesis. -/
lemma separated_replace_first {η δ : ℝ} {t : Triple} {x : E3}
    (hη : 0 < η) (ht : Separated η t)
    (hclose : dist x t.1 ≤ δ) (hδ : δ ≤ η / 2) :
    Separated (η / 2) (x, t.2) := by
  rcases t with ⟨a, b, c⟩
  rcases ht with ⟨hab, hac, hbc⟩
  have hx : dist a x ≤ δ := by simpa only [dist_comm] using hclose
  have hab' := dist_triangle a x b
  have hac' := dist_triangle a x c
  refine ⟨?_, ?_, ?_⟩ <;> dsimp at * <;> linarith

/-- Weakening separation to half its value. -/
lemma separated_half {η : ℝ} {t : Triple} (hη : 0 < η)
    (ht : Separated η t) : Separated (η / 2) t := by
  rcases ht with ⟨h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The two noncentral coordinates of a measure-valued lift preserve the marginal. -/
lemma preserves_coordinates {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {Q : E3 → Triple}
    (hQ : Measurable Q) (hmap : Measure.map Q μ = π) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) := by
  constructor
  · refine ⟨measurable_tripleSnd.comp hQ, ?_⟩
    rw [← Measure.map_map measurable_tripleSnd hQ, hmap]
    exact hπ.2.2.1
  · refine ⟨measurable_tripleThd.comp hQ, ?_⟩
    rw [← Measure.map_map measurable_tripleThd hQ, hmap]
    exact hπ.2.2.2

/-- A lift of a separated coupling, whose first coordinate remains nearby,
gives a finite-cost preserving pair and the quantitative Coulomb estimate. -/
theorem graph_cost_of_lift {μ : Measure E3} [IsProbabilityMeasure μ]
    {π : Measure Triple} (hπ : IsThreeCoupling μ π)
    {Q : E3 → Triple} (hQ : Measurable Q) (hmap : Measure.map Q μ = π)
    {η δ : ℝ} (hη : 0 < η) (hδ : δ ≤ η / 2)
    (hsep : ∀ᵐ t ∂π, Separated η t)
    (hclose : ∀ᵐ x ∂μ, dist x (Q x).1 ≤ δ) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) < ⊤ ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂π) + ENNReal.ofReal (24 * δ / η ^ 2) := by
  have hsepQ : ∀ᵐ x ∂μ, Separated η (Q x) :=
    ae_of_ae_map hQ.aemeasurable (by rwa [hmap])
  have hsepP : ∀ᵐ x ∂μ, Separated (η / 2) (x, (Q x).2) := by
    filter_upwards [hsepQ, hclose] with x hx hc
    exact separated_replace_first hη hx hc hδ
  have hsepQ' : ∀ᵐ x ∂μ, Separated (η / 2) (Q x) :=
    hsepQ.mono fun _ hx => separated_half hη hx
  have hc : ∀ᵐ x ∂μ, dist (x, (Q x).2).1 (Q x).1 ≤ δ ∧
      dist (x, (Q x).2).2.1 (Q x).2.1 ≤ δ ∧
      dist (x, (Q x).2).2.2 (Q x).2.2 ≤ δ := by
    filter_upwards [hclose] with x hx
    have hδ0 : 0 ≤ δ := dist_nonneg.trans hx
    exact ⟨hx, by simpa using hδ0, by simpa using hδ0⟩
  have hbound := lintegral_coulombCost_le_add_of_ae_close μ (half_pos hη)
    hsepP hsepQ' hc
  have herr : (6 * δ) / (η / 2) ^ 2 = 24 * δ / η ^ 2 := by
    field_simp
    ring
  rw [measure_univ, mul_one, herr] at hbound
  have hint : (∫⁻ x, coulombCost (Q x) ∂μ) = ∫⁻ t, coulombCost t ∂π := by
    rw [← lintegral_map measurable_coulombCost hQ, hmap]
  rw [hint] at hbound
  exact ⟨(preserves_coordinates hπ hQ hmap).1,
    (preserves_coordinates hπ hQ hmap).2,
    graphCost_lt_top_of_ae_separated μ (half_pos hη) hsepP, hbound⟩

end Problem356.FirstCoordinateLift

end

end OAI
