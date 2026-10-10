import OAI.Geometry.RCD.Metric.CompactFactorExtension
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace OAI

/-! # Bounded endpoint densities give genuine bounded L² initial data -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem compact_weighted_density_memLp {S : Set X} (hS : IsCompact S) (F : C(S, ℝ))
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {ρ : X → ℝ}
    (hρ : Measurable ρ) {C : ℝ} (hC : ∀ᵐ x ∂μ, |ρ x| ≤ C) :
    MemLp (fun x => ρ x*compactFactorExtension F x) 2 μ := by
  have htop : MemLp ρ ∞ μ := memLp_top_of_bound hρ.aestronglyMeasurable C hC
  change MemLp (ρ * compactFactorExtension F) 2 μ
  exact htop.mul (compactFactorExtension_memLp hS F μ)

omit [BorelSpace X] in
theorem compact_weighted_density_bounded {S : Set X} (hS : IsCompact S) (F : C(S, ℝ))
    (μ : Measure X) {ρ : X → ℝ} {C : ℝ≥0} (hC : ∀ᵐ x ∂μ, |ρ x| ≤ C) :
    ∃ D : ℝ≥0, ∀ᵐ x ∂μ, |ρ x*compactFactorExtension F x| ≤ D := by
  obtain ⟨B,hB⟩ := compactFactorExtension_bounded hS F
  refine ⟨C*B,?_⟩
  filter_upwards [hC] with x hx
  rw [abs_mul,NNReal.coe_mul]
  exact mul_le_mul hx (hB x) (abs_nonneg _) C.coe_nonneg

end RegularPointCoordinates

end

end OAI
