import OAI.Analysis.CircleDomains.Probability.PositiveCodeLawFusion
import OAI.Analysis.CircleDomains.Selection.CountableSetPresentation
import OAI.Analysis.CircleDomains.Probability.CountableLawRestriction
import OAI.Analysis.CircleDomains.Selection.CountableHitTests

namespace OAI

/-! Countable extraction supplies all tests in the fixed Borel candidate
family, so dust fusion retains the occupation and tuple density bounds. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] [Countable S]

theorem positive_code_law_of_countable_extraction
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hstandard : StandardBorelProbabilityLaws (BasePathCode d))
    (hpath : PolishProbabilityLaws C(PathTime, X))
    (a : S → X) (ha : Injective a) (haB : range a ⊆ d.dust)
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (E : ℝ≥0∞) (hE : E < ∞) {C : ℝ} (hC : 0 ≤ C)
    (hextract : ∀ (I : Set ℕ), IsClosed I → ∀ b : I → X, Injective b →
      range b ⊆ d.dust → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν d.dustᶜ = 0 →
        ∃ (P : ProbabilityMeasure (BasePathCode d)) (g : Y → ℝ≥0∞)
          (q : LevelTuple → ℝ≥0∞),
          Measurable g ∧ Measurable q ∧ meanCodeOccupation d P = μ.withDensity g ∧
          (∫⁻ y, g y ^ 2 ∂μ) ≤ E ∧
          countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (b s)) ≤
            ENNReal.ofReal C ∧
          meanCodeTuple d P = τ.withDensity q ∧ (∫⁻ t, q t ^ 2 ∂τ) ≤ E ∧
          (∫⁻ x, pathHitProbability (codePathLaw d P) x ∂ν) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P, CodeLawCandidate d a μ τ (densityMassBound μ E) (densityMassBound τ E)
        E ((ENNReal.ofReal C) ^ 2) P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ (C + ε) ^ 2) ∧
      {x : X | x ∈ d.dust ∧ 0 < pathHitProbability (codePathLaw d P) x}.Countable := by
  apply exists_codeLawCandidate_with_hit_bound d hU hB hstandard hpath a μ τ
    (densityMassBound μ E) (densityMassBound τ E) E ((ENNReal.ofReal C) ^ 2)
    (densityMassBound_lt_top μ hE) (densityMassBound_lt_top τ hE) hC _ hε
  intro D hD hDB ν hν hn hνB
  obtain ⟨I, b, hI, hb, hbD⟩ :=
    countableSetPresentation (D ∪ range a) (hD.union (countable_range a))
  have hbB : range b ⊆ d.dust := by
    rw [hbD]
    exact union_subset hDB haB
  obtain ⟨P, g, q, hg, hq, hocc, hgE, hv, htuple, hqE, hhit⟩ :=
    hextract I hI b hb hbB ν hν hn hνB
  have hab : range a ⊆ range b := by rw [hbD]; exact subset_union_right
  have hva : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤
      ENNReal.ofReal C :=
    (countingSquareNorm_restrict_range (meanVisitCount (codePathLaw d P)) a b ha hab).trans hv
  refine ⟨P, codeLawCandidate_of_extracted_bounds d a μ τ P hg hq hocc htuple hgE hqE hva,
    ?_, hhit⟩
  intro F hF
  exact finite_hit_square_sum_le_of_counting_norm (codePathLaw d P) b hC hv F
    (hF.trans (by rw [hbD]; exact subset_union_left))

end CircleDomainRigidity

end

end OAI
