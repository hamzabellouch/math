import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CoefficientStep

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy

def ModelAdmissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) : Prop :=
  ∀ π : Measure (Sphere d), IsProbabilityMeasure π → Admissible K ρ π

def FixedSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (ε : ℝ) (s : Sphere d) : ℝ≥0∞ :=
  let rowMeasurable := @MeasurableSpace.pi (Fin T) (fun _ => Vector d)
    (fun _ => @WithLp.measurableSpace
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (Fin d → ℝ) inferInstance)
  @lintegral (Ω × Rows d T)
    (@Prod.instMeasurableSpace Ω (Rows d T) inferInstance rowMeasurable)
    (@Measure.prod Ω (Rows d T) inferInstance rowMeasurable ρ (RowLaw d T))
    (fun z => experiment K (angleTest ε) (s,z))

lemma modelAdmissible_of_measurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω)
    (hc : ∀ᵐ ω ∂ρ, (K ω).Completed)
    (hm : ∀ f : Sphere d × Sphere d → ℝ≥0∞, Measurable f → (∀ x, f x ≤ 1) →
      Measurable (experiment K f)) : ModelAdmissible K ρ := by
  intro π hπ
  exact ⟨hc, fun f hf h1 => (hm f hf h1).aemeasurable⟩
end Policy
end MemoryPrecision.Kernel


end

end OAI
