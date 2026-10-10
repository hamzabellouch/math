import OAI.Analysis.CircleDomains.Probability.CountableVisitNorm

namespace OAI

/-! Square bounds on weights and mean visits give finite actual weighted
tolls almost surely. This retains all visits, including both endpoints. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tsum_mul_le_countingSquareNorm {A : Type*} [Countable A]
    (a b : A → ℝ≥0∞) :
    (∑' x, a x * b x) ≤ countingSquareNorm a * countingSquareNorm b := by
  let : MeasurableSpace A := ⊤
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := Measure.count)
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by constructor <;> norm_num)
    (measurable_of_countable a).aemeasurable (measurable_of_countable b).aemeasurable
  simpa only [Pi.mul_apply, ENNReal.rpow_two, lintegral_count, countingSquareNorm] using h

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem lintegral_boundaryToll_le_square_norms (μ : ProbabilityMeasure C(PathTime, X))
    (m : X → ℝ≥0∞) (hm : (support m).Countable) :
    (∫⁻ γ, boundaryToll γ m ∂(μ : Measure _)) ≤
      countingSquareNorm (fun x : support m => m x.val) *
      countingSquareNorm (fun x : support m => meanVisitCount μ x.val) := by
  let : Countable (support m) := hm.to_subtype
  rw [lintegral_boundaryToll μ hm]
  exact tsum_mul_le_countingSquareNorm _ _

theorem ae_boundaryToll_finite (μ : ProbabilityMeasure C(PathTime, X))
    (m : X → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), boundaryToll γ m < ∞ := by
  apply ae_lt_top (measurable_boundaryToll hm)
  exact ((lintegral_boundaryToll_le_square_norms μ m hm).trans_lt
    (ENNReal.mul_lt_top hweight hvisits)).ne

end CircleDomainRigidity

end

end OAI
