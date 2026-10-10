import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.QuadraticHyperplaneTangent
import OAI.Analysis.RieszRectifiability.Kernel.TranslatedRieszAnnuli

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem intrinsic_full_support_of_local_annular_bounds (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (hμ : μ ≠ 0)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ (p + 1) / C) ≤ μ (ball x R))
    (hannuli : ∀ a ∈ μ.support, ∃ R : ℝ, 0 < R ∧ ∃ B : ℝ,
      ∀ ε : ℝ, 0 < ε →
        ‖∫ y in ball a R ∩ {y | ε < dist y a}, kernel (p + 1) y a ∂μ‖ ≤ B) :
    μ.support = univ := by
  apply eq_univ_of_forall
  intro c
  by_contra hc
  obtain ⟨a, ha, hac, hmin⟩ := exists_nearest_point_to_hole μ.support μ.isClosed_support
    (μ.nonempty_support hμ) c hc
  obtain ⟨R, hR, B, hB⟩ := hannuli a ha
  let σ := blowupMeasure (p + 1) μ a 1
  have hgσ : GlobalUpperGrowth (p + 1) G σ :=
    blowupMeasure_growth (p + 1) μ a 1 G zero_lt_one hg
  have hlowerσ : ∀ x ∈ σ.support, ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (p + 1) / C) ≤ σ (ball x t) :=
    blowupMeasure_lower_global (p + 1) μ a 1 C zero_lt_one hlower
  have hzeroσ : (0 : Ambient (p + 1)) ∈ σ.support :=
    blowupMeasure_origin_mem_support (p + 1) μ a 1 zero_lt_one ha
  have hquad : ∀ x ∈ σ.support, 0 ≤ 2 * inner ℝ (a - c) x + ‖x‖ ^ 2 := by
    intro x hx
    have hsource := (blowupMeasure_support_iff (p + 1) μ a x 1 zero_lt_one).mp hx
    simpa only [one_mul] using! nearest_point_rescaled_constraint a c x 1 zero_lt_one
      (hmin (a + (1 : ℝ) • x) hsource)
  have hBσ : ∀ ε : ℝ, 0 < ε →
      ‖∫ x in ball (0 : Ambient (p + 1)) R ∩ {x | ε < ‖x‖}, kernel (p + 1) x 0 ∂σ‖ ≤ B := by
    intro ε hε
    dsimp only [σ]
    rw [translated_riesz_annulus_integral]
    exact hB ε hε
  exact intrinsic_quadratic_annular_bound_impossible p σ C G hC hgσ hlowerσ hzeroσ
    (a - c) (sub_ne_zero.mpr hac) hquad R B hR hBσ

end

end RieszRectifiability

end OAI
