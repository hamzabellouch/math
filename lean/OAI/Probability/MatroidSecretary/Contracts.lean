import OAI.Probability.MatroidSecretary.Selection.AveragedSafeExact
import OAI.Probability.MatroidSecretary.Accounting.SharpCost
import OAI.Probability.MatroidSecretary.Transport.StrongOneSample
import OAI.Probability.MatroidSecretary.Pivots.RawPatternCount
import OAI.Probability.MatroidSecretary.Residual.ExitSeries
import OAI.Probability.MatroidSecretary.Selection.CandidateContract
import OAI.Probability.MatroidSecretary.Accounting.MaximumWeighted
import OAI.Probability.MatroidSecretary.Accounting.ExpectedCost
import OAI.Probability.MatroidSecretary.Accounting.StrictSmallGroups
import OAI.Probability.MatroidSecretary.Accounting.Observation
import OAI.Probability.MatroidSecretary.Accounting.Threshold
import OAI.Probability.MatroidSecretary.Accounting.ConditionalExpectation
import OAI.Probability.MatroidSecretary.Sampling.SourceRankMask
import OAI.Probability.MatroidSecretary.Pivots.TransactionLogResource
import OAI.Probability.MatroidSecretary.Sampling.SourceSeedConditionalSupport
import OAI.Probability.MatroidSecretary.Secretary.CutoffLaw
import OAI.Probability.MatroidSecretary.Secretary.TripleKernel
import OAI.Probability.MatroidSecretary.Selection.FeasibilityContract
import OAI.Probability.MatroidSecretary.Selection.LayerImplementation
import OAI.Probability.MatroidSecretary.Transport.GeneralSimulation
import OAI.Probability.MatroidSecretary.Transport.SimulationInformation
import OAI.Probability.MatroidSecretary.Density.DensityContractsTheorems
import OAI.Probability.MatroidSecretary.Pivots.MarkedAuxiliaryAE
import OAI.Probability.MatroidSecretary.Pivots.RandomizedMarkedTransactions
import OAI.Probability.MatroidSecretary.Pivots.SupportedTransactions
import OAI.Probability.MatroidSecretary.Pivots.MarkedPivotContract
import OAI.Probability.MatroidSecretary.Pivots.MarkedPivotEdgeCases
import OAI.Probability.MatroidSecretary.Pivots.MarkedPivotFiniteOrder
import OAI.Probability.MatroidSecretary.Residual.ResidualFamilyContract
import OAI.Probability.MatroidSecretary.Pivots.PatternFamilySpecificationProof
import OAI.Probability.MatroidSecretary.Residual.FocalFamilyInvariance
import OAI.Probability.MatroidSecretary.Residual.ResidualTailEvent
import OAI.Probability.MatroidSecretary.Transport.TransferContract
import OAI.Probability.MatroidSecretary.Transport.TransferContracts
import OAI.Probability.MatroidSecretary.Selection.AssignedSafe
import OAI.Probability.MatroidSecretary.Secretary.Final
import OAI.Probability.MatroidSecretary.Accounting.Contracts
import OAI.Probability.MatroidSecretary.Residual.ExitContract
import OAI.Probability.MatroidSecretary.Selection.CandidateSpecificationTheorems
import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet.Assigned

open Finset MainAlgorithm MeasureTheory
attribute [local instance] Classical.propDecidable

theorem one_sample.{u} : MatroidProphet.OneSampleChallenge.{u} :=
  MatroidProphet.one_sample

theorem hidden_vector : MatroidProphet.HiddenVectorChallenge :=
  MatroidProphet.hidden_vector

/-- Source `lem:filter`: actual priority-greedy survivors and candidate mass. -/
theorem filter : MatroidProphet.CandidateSpecification.CandidateMass := MatroidProphet.CandidateSpecification.candidateMass

/-- Source `lem:density`: concrete largest optimizer and its residual bound. -/
theorem density {α : Type*} [Fintype α] (M : Matroid α)
    (hE : M.E = Set.univ) (κ : ℕ) (D : Set α) :
    DensityExpansionContract M hE κ D := source_density_expansion M hE κ D

/-- Source `lem:paths`: the full integer timeline, including least births. -/
theorem paths {α : Type*} [Fintype α] (M : Matroid α)
    (hE : M.E = Set.univ) (κ : ℕ) (D C : ℕ → Set α) :
    PathPropertiesContract M hE κ D C := source_path_properties M hE κ D C

/-- Source `lem:generators`: one increasing generator family and one total budget. -/
theorem generators {α : Type*} [Fintype α] (M : Matroid α)
    (hE : M.E = Set.univ) (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) :
    GeneratorBudgetContract M hE κ D C := source_generator_budget M hE κ hκ D C

theorem all_orders {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) :
    (∀ π : ArrivalOrder n, listedLambda M hE d w h ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card) ∧
    (∀ A : Finset (Fin n), Disjoint A (pathGroups M d w h) →
      thinningRate * (finalRankStatistic M hE (2^100)
        (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (A : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n)))
        h (groups M d w).length (pathGroups M d w h)
        ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) Set.univ
        (boolParity d.odd) : ℝ) ≤
      bitsExpectation (fun _ : Fin n => thinningRate) (pathGroups M d w h)
        (fun B => (listedLambda M hE {d with T := A ∪ B} w h : ℝ))) := AccountingContracts.all_orders M hE d w h

theorem rank_cost {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ)
    (hh : h < (groups M d w).length) :
    (listedZ M hE d w h : ℝ) ≤
      (finalRankStatistic M hE (2^100) (groupMask M d w d.D)
        (groupMask M d w d.C) (groupMask M d w d.T) h (groups M d w).length
        (groupMask M d w univ h)
        ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) Set.univ
        (boolParity d.odd) : ℝ) + (groupMask M d w d.C h).ncard +
      ∑ j ∈ range ((groups M d w).length-(h+1)),
        ((groupMask M d w d.C (h+1+j)).ncard +
          (groupMask M d w d.D (h+1+j)).ncard / densityThreshold) := AccountingContracts.rank_cost M hE d w h hh

theorem exit {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) :
    (∀ C : Finset α,
      ∃ t ∈ reverseTrace M hE κ D G h (pathHorizon h + 1) (-1)
          (fun _ => Set.univ) C, d ∈ t.before h ∧ d ∉ t.after h) ∧
    bitsExpectation q univ (fun C =>
      if ∃ t ∈ reverseTrace M hE κ D G h (pathHorizon h + 1) (-1)
          (fun _ => Set.univ) C,
        d ∈ t.before h ∧ d ∉ t.after h ∧
          reverseHazard M hE κ D G q d h t.time t.before < exitThreshold
      then (1 : ℝ) else 0) < 1 / 2 ∧
    exitThreshold / 2 ≤ ∑ i ∈ range (pathHorizon h + 1),
      bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := ExitContract.exit_mass_actual M hE κ D G hG q hq0 hq1 d hd h

theorem secretary.{u} : MatroidProphet.SecretaryChallenge.{u} :=
  MatroidProphet.secretary

theorem simulation.{u,v} : General.SimulationContract.{u,v} := General.simulation_contract

theorem feasibility {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    MainRuleFeasibility M (MainAlgorithm.hidden M hE) := FeasibilityContract.source_main_feasibility M hE

theorem safe : SafeSampleClaim := MainAlgorithm.safe_sampled_labels_claim

theorem pivot_patterns.{u} : MarkedPivots.SourceContract.{u} := MarkedPivots.sourceContract

theorem pattern_family : PatternFamilyClaim := MainAlgorithm.pattern_family_claim

theorem transfer : TransferClaim := SourceProof.transfer_claim

theorem transactions
    {α : Type*} [Fintype α] [DecidableEq α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (prog : Ω → MarkedQueryProgram α)
    (fresh : ∀ ω, (prog ω).Fresh univ)
    (sound : ∀ ω S, 0 < bitsWeight q univ S → (prog ω).SoundAt cert S ∅)
    (meas : ∀ S, Measurable (fun ω => (prog ω).run S)) :
    Integrable (fun ω => bitsExpectation q univ (prog ω).run) μ ∧
    (∫ ω, bitsExpectation q univ (prog ω).run ∂μ) ≤
      Real.log (1 / bitsFailure cert q univ ∅) := MarkedQueryProgram.disjoint_query_certificates_auxiliary cert hcert q hq0 hq1 hδ μ prog fresh sound meas

end MatroidProphet.Assigned

end OAI
