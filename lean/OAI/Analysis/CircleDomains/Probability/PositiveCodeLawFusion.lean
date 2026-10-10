import OAI.Analysis.CircleDomains.Probability.BorelFamilyHitFusion
import OAI.Analysis.CircleDomains.Probability.CodeLawCandidates

namespace OAI

/-! Fusion within the actual occupation/visit/tuple candidate family. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] [Countable S]

theorem exists_codeLawCandidate_with_hit_bound
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hstandard : StandardBorelProbabilityLaws (BasePathCode d))
    (hpath : PolishProbabilityLaws C(PathTime, X))
    (a : S → X) (μ : Measure Y) [IsFiniteMeasure μ]
    (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (M N E V : ℝ≥0∞) (hM : M < ∞) (hN : N < ∞)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → D ⊆ d.dust → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν d.dustᶜ = 0 →
        ∃ P, CodeLawCandidate d a μ τ M N E V P ∧
          PassesHitTests C (codePathLaw d P) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P, CodeLawCandidate d a μ τ M N E V P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ (C + ε) ^ 2) ∧
      {x : X | x ∈ d.dust ∧ 0 < pathHitProbability (codePathLaw d P) x}.Countable := by
  exact exists_law_in_borel_family_with_hit_bound hstandard hpath
    {P | CodeLawCandidate d a μ τ M N E V P}
    (measurableSet_codeLawCandidate d hU a μ τ M N E V hM hN)
    (codePath d) (measurable_codePath d)
    (fun P law hlaw h => CodeLawCandidate.mixture d hU a μ τ M N E V hM hN
      P law hlaw h) d.dust hB hC htest hε

end CircleDomainRigidity

end

end OAI
