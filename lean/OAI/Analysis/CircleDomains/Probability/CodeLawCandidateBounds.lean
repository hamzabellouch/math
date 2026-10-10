import OAI.Analysis.CircleDomains.Probability.CodeLawCandidates
import OAI.Analysis.CircleDomains.Probability.DensityMassBound
import OAI.Analysis.CircleDomains.Probability.CountableVisitNorm

namespace OAI

/-! The quantitative outputs of countable modulus extraction are members of
one fixed candidate family, independent of the prescribed countable set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanVisitCount_codePathLaw_eq_integral (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) (s : S) :
    meanVisitCount (codePathLaw d P) (a s) =
      ∫⁻ Γ, codeVisitWeight d a s Γ ∂(P : Measure (BasePathCode d)) := by
  have hv : Measurable (fun γ : C(PathTime, X) => visitCount γ (a s)) :=
    measurable_visitCount.comp (measurable_id.prodMk measurable_const)
  unfold meanVisitCount codePathLaw
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hv (measurable_codePath d)]
  rfl

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem countableSquareLawBounds_of_visit_norm (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) {C : ℝ≥0∞}
    (h : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤ C) :
    CountableSquareLawBounds (codeVisitWeight d a) (C ^ 2) P := by
  intro F
  simp_rw [← meanVisitCount_codePathLaw_eq_integral]
  have he : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ^ 2 =
      ∑' s, meanVisitCount (codePathLaw d P) (a s) ^ 2 := by
    rw [countingSquareNorm, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  exact (ENNReal.sum_le_tsum F).trans (he ▸ pow_le_pow_left' h 2)

omit [SecondCountableTopology Y] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] in
theorem codeLawCandidate_of_extracted_bounds (d : PathCodeData X Y)
    (a : S → X) (μ : Measure Y) (τ : Measure LevelTuple)
    (P : ProbabilityMeasure (BasePathCode d))
    {g : Y → ℝ≥0∞} {q : LevelTuple → ℝ≥0∞} (hg : Measurable g) (hq : Measurable q)
    (hocc : meanCodeOccupation d P = μ.withDensity g)
    (htuple : meanCodeTuple d P = τ.withDensity q)
    {E C : ℝ≥0∞} (hgE : (∫⁻ y, g y ^ 2 ∂μ) ≤ E)
    (hqE : (∫⁻ t, q t ^ 2 ∂τ) ≤ E)
    (hv : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤ C) :
    CodeLawCandidate d a μ τ (densityMassBound μ E) (densityMassBound τ E) E (C ^ 2) P :=
  ⟨boundedDensityBudget_of_square_bound μ _ hg hocc hgE,
    countableSquareLawBounds_of_visit_norm d P a hv,
    boundedDensityBudget_of_square_bound τ _ hq htuple hqE⟩

end CircleDomainRigidity

end

end OAI
