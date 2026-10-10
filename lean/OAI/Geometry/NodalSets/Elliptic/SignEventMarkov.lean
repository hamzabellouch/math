import OAI.Geometry.NodalSets.Waves.GaussianGradientSupremum

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

lemma event_inter_gradient_bound {A : Set Ω} {G : Ω → ℝ}
    (hG : Integrable G μ) (hG0 : ∀ x, 0 ≤ G x) {L : ℝ} (hL : 0 < L) :
    μ.real A - (∫ x, G x ∂μ)/L ≤ μ.real (A ∩ {x | G x ≤ L}) := by
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hG0) hG L
  have htail : μ.real {x | L ≤ G x} ≤ (∫ x, G x ∂μ)/L := by
    apply (le_div_iff₀ hL).mpr
    linarith
  have hcover : A ⊆ (A ∩ {x | G x ≤ L}) ∪ {x | L ≤ G x} := by
    intro x hx
    by_cases hh : G x ≤ L
    · exact Or.inl ⟨hx,hh⟩
    · exact Or.inr (le_of_lt (lt_of_not_ge hh))
  have hmeasure := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le (μ := μ) _ _)
  linarith

lemma event_inter_gradient_half {A : Set Ω} {G : Ω → ℝ}
    (hG : Integrable G μ) (hG0 : ∀ x, 0 ≤ G x) {p L : ℝ} (hL : 0 < L)
    (hA : p ≤ μ.real A) (hmean : 2*(∫ x, G x ∂μ) ≤ p*L) :
    p/2 ≤ μ.real (A ∩ {x | G x ≤ L}) := by
  have h := event_inter_gradient_bound (A := A) hG hG0 hL
  have hratio : (∫ x, G x ∂μ)/L ≤ p/2 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  linarith

end
end Yau.Geometry

end OAI
