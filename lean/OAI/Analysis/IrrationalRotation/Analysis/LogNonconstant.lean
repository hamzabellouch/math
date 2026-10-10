import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Analysis.CountableFiberAtoms

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem not_ae_constant_of_positive_of_infiniteLog [IsProbabilityMeasure μ]
    {f : X → ℝ} (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : HasNegInfiniteLogIntegral μ f) :
    ¬ ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  rintro ⟨c, hc⟩
  have hcpos : 0 < c := by
    obtain ⟨x, hx, hxc⟩ := (hpos.and hc).exists
    simpa only [hxc] using hx
  have hlin : (∫⁻ x, negLogCost (f x) ∂μ) = negLogCost c := by
    calc
      (∫⁻ x, negLogCost (f x) ∂μ) = ∫⁻ _x, negLogCost c ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hc] with x hx
        rw [hx]
      _ = negLogCost c := by simp
  have hfinite : negLogCost c ≠ ∞ := by
    rw [negLogCost, ite_eq_right (ne_of_gt hcpos)]
    exact ENNReal.ofReal_ne_top
  exact hfinite (hlin.symm.trans hinf)

theorem exists_nontrivial_level_of_positive_of_infiniteLog [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : HasNegInfiniteLogIntegral μ f)
    (hcount : ∃ C : Set ℝ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C) :
    ∃ c : ℝ, MeasurableSet (f ⁻¹' {c}) ∧
      μ (f ⁻¹' {c}) ≠ 0 ∧ μ (f ⁻¹' {c})ᶜ ≠ 0 := by
  obtain ⟨C, hC, hmem⟩ := hcount
  obtain ⟨c, _, hc, hc'⟩ :=
    InvariantProjection.CountableFiberAtoms.exists_nontrivial_fiber hC hmem
      (not_ae_constant_of_positive_of_infiniteLog hpos hinf)
  exact ⟨c, hf (measurableSet_singleton c), hc, hc'⟩

end Invariant233

end OAI
