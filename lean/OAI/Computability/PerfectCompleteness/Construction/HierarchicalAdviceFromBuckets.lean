import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalUsefulCollision
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAdviceFromBuckets

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {Ω P : Type*}
  [Fintype Ω] [Fintype P]
  (S : HierarchicalAdviceExperiment.Experiment branch rows n t Ω)

local instance backgroundFintype : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace S.slots S.upper) :=
  Fintype.ofFinite _

local instance inputFintype :
    (b : HierarchicalAdviceExperiment.Background S) → Fintype (HierarchicalAdviceExperiment.Input S b) :=
  HierarchicalAdviceExperiment.inputFintype S

local instance inputFiniteDimensional :
    (b : HierarchicalAdviceExperiment.Background S) →
      FiniteDimensional F2 (HierarchicalAdviceExperiment.Input S b) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional S

def backgroundLaw (externalLaw : FiniteDistribution P)
    (background : P → HierarchicalAdviceExperiment.Background S) :
    FiniteDistribution (HierarchicalAdviceExperiment.Background S) :=
  externalLaw.pushforward background

def pairedLaw (externalLaw : FiniteDistribution P)
    (background : P → HierarchicalAdviceExperiment.Background S)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace S.slots S.upper))
    (hrows : 0 < rows (Nodes.height S.upper)) :=
  HierarchicalUsefulCollision.pairLaw S.slots S.upper externalLaw background scalarLaw hrows

def usefulProbability (κ : ℝ) (externalLaw : FiniteDistribution P)
    (background : P → HierarchicalAdviceExperiment.Background S)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace S.slots S.upper))
    (hrows : 0 < rows (Nodes.height S.upper)) : ℝ :=
  (HierarchicalUsefulCollision.law S.slots S.upper externalLaw scalarLaw hrows).probability
    (HierarchicalUsefulCollision.usefulEvent S.slots S.upper S.lowerLevel S.original S.arrays
      (HierarchicalAdviceExperiment.lowerEvent S) κ S.strategy background)

def adviceFactor (r : Nat) (η : ℝ) : ℝ :=
  (η ^ 2 / 4) / ((2 : ℝ) ^ (r * rows (Nodes.height S.upper))) ^ 2

variable (κ : ℝ) (externalLaw : FiniteDistribution P)
  (background : P → HierarchicalAdviceExperiment.Background S)
  (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace S.slots S.upper))
  (hrows : 0 < rows (Nodes.height S.upper))

theorem mean_agreement_ge (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulProbability S κ externalLaw background scalarLaw hrows)
    (hpaired : (pairedLaw S externalLaw background scalarLaw hrows).totalVariation
      (HierarchicalAgreementMean.referenceLaw S.slots S.upper
        (backgroundLaw S externalLaw background) hrows) ≤ c ^ 2 / 16) :
    c ^ 2 / 16 ≤ (backgroundLaw S externalLaw background).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceExperiment.table S κ b)) := by
  have hcollision := HierarchicalUsefulCollision.collision_probability_ge_eighth
    S.slots S.upper S.lowerLevel S.original S.arrays
    (HierarchicalAdviceExperiment.lowerEvent S) κ S.strategy externalLaw background scalarLaw
    hrows c hc hmass
  have hmean := HierarchicalAgreementMean.mean_nonzeroAgreement_ge_sixteenth
    S.slots S.upper S.lowerLevel S.original S.arrays
    (HierarchicalAdviceExperiment.lowerEvent S) κ S.strategy
    (backgroundLaw S externalLaw background) hrows
    (pairedLaw S externalLaw background scalarLaw hrows) c hcollision hpaired
  change 2 * (c ^ 2 / 32) ≤
    (backgroundLaw S externalLaw background).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceExperiment.table S κ b)) at hmean
  linarith

theorem prediction_difference (hκ : 0 ≤ κ)
    (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulProbability S κ externalLaw background scalarLaw hrows)
    (hpaired : (pairedLaw S externalLaw background scalarLaw hrows).totalVariation
      (HierarchicalAgreementMean.referenceLaw S.slots S.upper
        (backgroundLaw S externalLaw background) hrows) ≤ c ^ 2 / 16)
    (r : Nat) (ρ η v : ℝ) (hη : 0 < η) (hηbound : 2 * η ≤ c ^ 2 / 16)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hv : 0 ≤ v) (hsmall : v ≤ ρ * adviceFactor S r η / 16)
    (hcoarse : ((HierarchicalAdviceExperiment.originalLaw S r).pushforward
      (HierarchicalAdviceExperiment.observe S r)).totalVariation
      ((HierarchicalAdviceExperiment.referenceLaw S (backgroundLaw S externalLaw background) r).pushforward (HierarchicalAdviceExperiment.referenceObserve S r)) ≤ v) :
    κ * ρ * adviceFactor S r η / 4 ≤
      (HierarchicalAdviceExperiment.originalLaw S r).probability
        (HierarchicalAdviceExperiment.prediction S κ r ρ) -
      (κ * ρ / 4) * (HierarchicalAdviceExperiment.originalLaw S r).probability
        (fun x => HierarchicalAdviceExperiment.J S κ r ρ
          (HierarchicalAdviceExperiment.observe S r x)) := by
  exact HierarchicalAdviceExperiment.prediction_difference S κ hκ
    (backgroundLaw S externalLaw background) hrows r ρ η v hη hρ hρ1 hconstants
    (hηbound.trans (mean_agreement_ge S κ externalLaw background scalarLaw hrows
      c hc hmass hpaired)) hv hsmall hcoarse

theorem good_record_mass_ge {R : Type*} [Fintype R]
    (hκ : 0 ≤ κ) (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulProbability S κ externalLaw background scalarLaw hrows)
    (hpaired : (pairedLaw S externalLaw background scalarLaw hrows).totalVariation
      (HierarchicalAgreementMean.referenceLaw S.slots S.upper
        (backgroundLaw S externalLaw background) hrows) ≤ c ^ 2 / 16)
    (r : Nat) (ρ η v : ℝ) (hη : 0 < η) (hηbound : 2 * η ≤ c ^ 2 / 16)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hv : 0 ≤ v) (hsmall : v ≤ ρ * adviceFactor S r η / 16)
    (hcoarse : ((HierarchicalAdviceExperiment.originalLaw S r).pushforward
      (HierarchicalAdviceExperiment.observe S r)).totalVariation
      ((HierarchicalAdviceExperiment.referenceLaw S (backgroundLaw S externalLaw background) r).pushforward (HierarchicalAdviceExperiment.referenceObserve S r)) ≤ v)
    (record : Ω × HierarchicalAdviceExperiment.Advice S r → R) :
    κ * ρ * adviceFactor S r η / 4 ≤
      (HierarchicalAdviceExperiment.originalLaw S r).probability
        (fun x => HierarchicalAdviceExperiment.J S κ r ρ
          (HierarchicalAdviceExperiment.observe S r x) &&
          PositiveFiberMass.goodRecord (HierarchicalAdviceExperiment.originalLaw S r) record
            (fun y => HierarchicalAdviceExperiment.J S κ r ρ
              (HierarchicalAdviceExperiment.observe S r y))
            (HierarchicalAdviceExperiment.prediction S κ r ρ) (κ * ρ / 4) (record x)) :=
  (prediction_difference S κ externalLaw background scalarLaw hrows hκ c hc hmass hpaired
    r ρ η v hη hηbound hρ hρ1 hconstants hv hsmall hcoarse).trans
    (HierarchicalAdviceExperiment.prediction_difference_le_good_mass S κ hκ r ρ hρ.le record)

end
end PerfectCompleteness.HierarchicalAdviceFromBuckets

end

end OAI
