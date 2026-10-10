import OAI.Computability.PerfectCompleteness.Algebra.TensorBucketEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GoodAdviceEventsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HeterogeneousAdviceFamily
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalPrediction
import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas
import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas

namespace OAI


namespace PerfectCompleteness.HierarchicalAdviceExperiment

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

structure Experiment (branch rows : Nat → Nat) (n t : Nat) (Ω : Type*) [Fintype Ω] where
  slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot
  upper : Nodes branch n
  lowerLevel : Nat
  arrays : Ω → Arrays slots rows
  lowerNode : Ω → Nodes branch n
  separate : ∀ x, upper ≠ lowerNode x
  direction : ∀ x, Block rows (lowerNode x)
  original : FiniteDistribution Ω
  strategy : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)

variable {branch rows : Nat → Nat} {n t : Nat} {Ω : Type*} [Fintype Ω]
  (S : Experiment branch rows n t Ω)

abbrev Background := HierarchicalMatrixTable.Background (rows := rows) S.slots S.upper

local instance backgroundFintype : Fintype (Background S) := Fintype.ofFinite _

abbrev Input (background : Background S) :=
  Module.Dual F2 (NodeEmbedding.RowSpace S.slots S.upper ⧸
    HierarchicalFrozenTables.knownRows S.slots S.upper S.lowerLevel background)

local instance inputFintype : (b : Background S) → Fintype (Input S b) :=
  fun _ => linearMapFintype

local instance inputFiniteDimensional :
    (b : Background S) → FiniteDimensional F2 (Input S b) :=
  fun _ => inferInstance

abbrev Value := Block rows S.upper × HierarchicalMatrixTable.SideOutput (rows := rows) S.upper

local instance valueFintype : Fintype (Value S) := Fintype.ofFinite _

abbrev Advice (r : Nat) := ManyGoodRows.RowMap (Block rows S.upper) r
abbrev Coarse := HierarchicalUsefulness.Coarse (rows := rows) S.slots S.upper S.lowerLevel
abbrev ReferenceSample (r : Nat) :=
  GoodAdviceFamily.Sample (E := Input S) (F := Block rows S.upper) r

def background (x : Ω) : Background S :=
  HierarchicalMatrixTable.backgroundOf S.slots S.upper (S.arrays x)

def matrix (x : Ω) : HierarchicalMatrixTable.Matrix (rows := rows) S.slots S.upper :=
  NodeEmbedding.matrix (S.arrays x) S.upper

def coarse (x : Ω) : Coarse S :=
  HierarchicalUsefulness.observe S.slots S.upper S.lowerLevel (S.arrays x)

def lowerEvent (x : Ω) : Bool :=
  decide (HierarchicalPrediction.LowerAccepts S.slots S.upper (background S x)
    S.strategy (S.lowerNode x) (S.direction x) (matrix S x))

def table (κ : ℝ) (b : Background S) :
    (Input S b →ₗ[F2] Block rows S.upper) → Option (Value S) :=
  HierarchicalUsefulness.table S.slots S.upper S.lowerLevel S.original S.arrays
    (lowerEvent S) κ S.strategy b

def J (κ : ℝ) (r : Nat) (ρ : ℝ) (z : Coarse S × Advice S r) : Bool :=
  GoodAdviceEvents.J (table S κ z.1.1) r ρ (z.2, z.1.2)

def I (κ : ℝ) (r : Nat) (ρ : ℝ) (z : Coarse S × Advice S r) : Bool :=
  GoodAdviceEvents.I (table S κ z.1.1) r ρ (z.2, z.1.2)

def adviceLaw (r : Nat) : FiniteDistribution (Advice S r) :=
  FiniteDistribution.uniform _

def originalLaw (r : Nat) : FiniteDistribution (Ω × Advice S r) :=
  S.original.product (adviceLaw S r)

def observe (r : Nat) (x : Ω × Advice S r) : Coarse S × Advice S r :=
  (coarse S x.1, x.2)

def referenceLaw (backgroundLaw : FiniteDistribution (Background S)) (r : Nat) :
    FiniteDistribution (ReferenceSample S r) :=
  GoodAdviceFamily.law backgroundLaw r

def referenceObserve (r : Nat) (x : ReferenceSample S r) : Coarse S × Advice S r :=
  (⟨x.1, x.2.2⟩, x.2.1)

def prediction (κ : ℝ) (r : Nat) (ρ : ℝ) (x : Ω × Advice S r) : Bool :=
  HierarchicalPrediction.prediction S.slots S.upper S.lowerLevel (background S x.1)
    S.strategy (S.lowerNode x.1) (S.separate x.1) (S.direction x.1)
    S.original S.arrays (lowerEvent S) κ r ρ x.2 (matrix S x.1)

theorem I_implies_mark (κ : ℝ) (r : Nat) (ρ : ℝ) (z : Coarse S) (A : Advice S r)
    (hI : I S κ r ρ (z, A) = true) :
    UsefulMark.useful S.original (coarse S) (lowerEvent S) κ z = true := by
  obtain ⟨y, _, hy⟩ := HierarchicalPrediction.selectedValue_of_I
    (table S κ z.1) r ρ A z.2 hI
  have hsome := congrArg Option.isSome hy
  change (HierarchicalUsefulness.table S.slots S.upper S.lowerLevel S.original S.arrays
    (lowerEvent S) κ S.strategy z.1 z.2).isSome = true at hsome
  rw [HierarchicalUsefulness.table_isSome] at hsome
  exact hsome

theorem lower_I_implies_prediction (κ : ℝ) (r : Nat) (ρ : ℝ)
    (x : Ω) (A : Advice S r) (hL : lowerEvent S x = true)
    (hI : I S κ r ρ (coarse S x, A) = true) :
    prediction S κ r ρ (x, A) = true := by
  exact HierarchicalPrediction.lower_accepts_predicts S.slots S.upper S.lowerLevel
    (background S x) S.strategy (S.lowerNode x) (S.separate x) (S.direction x)
    S.original S.arrays (lowerEvent S) κ r ρ A (matrix S x)
    (of_decide_eq_true hL) (by
      simpa only [I, table, coarse, HierarchicalUsefulness.observe, background, matrix,
        HierarchicalPrediction.quotientMatrix, inputFintype] using! hI)

theorem prediction_implies_J (κ : ℝ) (r : Nat) (ρ : ℝ)
    (x : Ω × Advice S r) (hp : prediction S κ r ρ x = true) :
    J S κ r ρ (observe S r x) = true := by
  simpa only [J, table, observe, coarse, HierarchicalUsefulness.observe, background, matrix,
    HierarchicalPrediction.quotientMatrix, inputFintype] using! (Bool.and_eq_true_iff.mp hp).1

theorem reference_J_mass_ge (κ : ℝ)
    (backgroundLaw : FiniteDistribution (Background S))
    (hrows : 0 < rows (Nodes.height S.upper))
    (r : Nat) (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ backgroundLaw.expectation (fun b =>
      PartialTableInverse.nonzeroAgreement (table S κ b))) :
    (η ^ 2 / 4) / ((2 : ℝ) ^ (r * rows (Nodes.height S.upper))) ^ 2 ≤
      (referenceLaw S backgroundLaw r).probability
        (fun x => J S κ r ρ (referenceObserve S r x)) := by
  let : Nonempty (Fin (rows (Nodes.height S.upper))) := ⟨⟨0, hrows⟩⟩
  have h := GoodAdviceFamily.J_probability_ge backgroundLaw (table S κ)
    r ρ η hη hρ hρ1 hconstants hmean
  have hevent : GoodAdviceFamily.J (table S κ) r ρ =
      (fun x : ReferenceSample S r => J S κ r ρ (referenceObserve S r x)) := by
    funext x
    rfl
  rw [hevent] at h
  simpa only [referenceLaw, Block, Module.finrank_fin_fun] using h

theorem prediction_difference (κ : ℝ) (hκ : 0 ≤ κ)
    (backgroundLaw : FiniteDistribution (Background S))
    (hrows : 0 < rows (Nodes.height S.upper))
    (r : Nat) (ρ η v : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ backgroundLaw.expectation (fun b =>
      PartialTableInverse.nonzeroAgreement (table S κ b)))
    (hv : 0 ≤ v)
    (hsmall : v ≤ ρ * ((η ^ 2 / 4) /
      ((2 : ℝ) ^ (r * rows (Nodes.height S.upper))) ^ 2) / 16)
    (hvariation : ((originalLaw S r).pushforward (observe S r)).totalVariation
      ((referenceLaw S backgroundLaw r).pushforward (referenceObserve S r)) ≤ v) :
    κ * ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * rows (Nodes.height S.upper))) ^ 2) / 4 ≤
      (originalLaw S r).probability (prediction S κ r ρ) -
        (κ * ρ / 4) * (originalLaw S r).probability
          (fun x => J S κ r ρ (observe S r x)) := by
  apply PredictionDifference.of_original_usefulness S.original (adviceLaw S r)
    (referenceLaw S backgroundLaw r) (coarse S) (referenceObserve S r)
    (lowerEvent S) (I S κ r ρ) (J S κ r ρ) (prediction S κ r ρ)
    κ ρ ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * rows (Nodes.height S.upper))) ^ 2)
    v hκ hρ.le hρ1.le (by positivity) hv hsmall
  · exact I_implies_mark S κ r ρ
  · exact lower_I_implies_prediction S κ r ρ
  · exact hvariation
  · exact reference_J_mass_ge S κ backgroundLaw hrows r ρ η hη hρ hρ1 hconstants hmean
  · exact GoodAdviceFamily.I_probability_ge backgroundLaw (table S κ) r ρ

theorem prediction_difference_le_good_mass {R : Type*} [Fintype R]
    (κ : ℝ) (hκ : 0 ≤ κ) (r : Nat) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (record : Ω × Advice S r → R) :
    (originalLaw S r).probability (prediction S κ r ρ) -
        (κ * ρ / 4) * (originalLaw S r).probability
          (fun x => J S κ r ρ (observe S r x)) ≤
      (originalLaw S r).probability (fun x => J S κ r ρ (observe S r x) &&
        PositiveFiberMass.goodRecord (originalLaw S r) record
          (fun y => J S κ r ρ (observe S r y)) (prediction S κ r ρ)
          (κ * ρ / 4) (record x)) := by
  have hevent : (fun x => J S κ r ρ (observe S r x) && prediction S κ r ρ x) =
      prediction S κ r ρ := by
    funext x
    by_cases hp : prediction S κ r ρ x = true
    · simp only [hp, prediction_implies_J S κ r ρ x hp, Bool.true_and]
    · have hp' : prediction S κ r ρ x = false := Bool.eq_false_iff.mpr hp
      simp only [hp', Bool.and_false]
  have h := PositiveFiberMass.difference_le_good_mass (originalLaw S r) record
    (fun x => J S κ r ρ (observe S r x)) (prediction S κ r ρ)
    (κ * ρ / 4) (by positivity)
  rw [hevent] at h
  exact h

end
end PerfectCompleteness.HierarchicalAdviceExperiment


namespace PerfectCompleteness.HierarchicalAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Fourier.MatrixLevelBridge

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

abbrev Background := (o : O) × HierarchicalAdviceExperiment.Background (S o)

local instance backgroundFiberFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

abbrev Input (b : Background S) := HierarchicalAdviceExperiment.Input (S b.1) b.2
abbrev Row (b : Background S) := Block rows (S b.1).upper
abbrev Value (b : Background S) := HierarchicalAdviceExperiment.Value (S b.1)

local instance inputFintype (b : Background S) : Fintype (Input S b) :=
  HierarchicalAdviceExperiment.inputFintype (S b.1) b.2

local instance inputFiniteDimensional (b : Background S) : FiniteDimensional F2 (Input S b) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional (S b.1) b.2

local instance valueFintype (b : Background S) : Fintype (Value S b) :=
  HierarchicalAdviceExperiment.valueFintype (S b.1)

def table (κ : ℝ) (b : Background S) :
    (Input S b →ₗ[F2] Row S b) → Option (Value S b) :=
  HierarchicalAdviceExperiment.table (S b.1) κ b.2

abbrev OriginalSample (r : Nat) :=
  (o : O) × (Ω o × HierarchicalAdviceExperiment.Advice (S o) r)

abbrev Observation (r : Nat) :=
  (o : O) × (HierarchicalAdviceExperiment.Coarse (S o) ×
    HierarchicalAdviceExperiment.Advice (S o) r)

local instance coarseFintype (o : O) : Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalUsefulness.coarseFintype (rows := rows) (S o).slots (S o).upper (S o).lowerLevel

abbrev ReferenceSample (r : Nat) :=
  HeterogeneousAdviceFamily.Sample (E := Input S) (F := Row S) r

def originalLaw (outer : FiniteDistribution O) (r : Nat) :
    FiniteDistribution (OriginalSample S r) :=
  CompletionSoundness.sigmaLaw outer (fun o => HierarchicalAdviceExperiment.originalLaw (S o) r)

def observe (r : Nat) (x : OriginalSample S r) : Observation S r :=
  ⟨x.1, HierarchicalAdviceExperiment.observe (S x.1) r x.2⟩

def backgroundLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o))) :
    FiniteDistribution (Background S) :=
  CompletionSoundness.sigmaLaw outer backgrounds

def referenceLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (r : Nat) : FiniteDistribution (ReferenceSample S r) :=
  HeterogeneousAdviceFamily.law (backgroundLaw S outer backgrounds) r

def referenceObserve (r : Nat) (x : ReferenceSample S r) : Observation S r :=
  ⟨x.1.1, (⟨x.1.2, x.2.2⟩, x.2.1)⟩

def J (κ : ℝ) (r : Nat) (ρ : ℝ) (z : Observation S r) : Bool :=
  HierarchicalAdviceExperiment.J (S z.1) κ r ρ z.2

def I (κ : ℝ) (r : Nat) (ρ : ℝ) (z : Observation S r) : Bool :=
  HierarchicalAdviceExperiment.I (S z.1) κ r ρ z.2

def prediction (κ : ℝ) (r : Nat) (ρ : ℝ) (x : OriginalSample S r) : Bool :=
  HierarchicalAdviceExperiment.prediction (S x.1) κ r ρ x.2

omit [Fintype O] in
theorem reference_J (κ : ℝ) (r : Nat) (ρ : ℝ) (x : ReferenceSample S r) :
    J S κ r ρ (referenceObserve S r x) =
      HeterogeneousAdviceFamily.J (table S κ) r ρ x := rfl

omit [Fintype O] in
theorem reference_I (κ : ℝ) (r : Nat) (ρ : ℝ) (x : ReferenceSample S r) :
    I S κ r ρ (referenceObserve S r x) =
      HeterogeneousAdviceFamily.I (table S κ) r ρ x := rfl

theorem reference_J_mass_ge (κ : ℝ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))
    (ℓ : Nat) (hdim : ∀ o, rows (Nodes.height (S o).upper) ≤ ℓ)
    (r : Nat) (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ (backgroundLaw S outer backgrounds).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (table S κ b))) :
    (η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2 ≤
      (referenceLaw S outer backgrounds r).probability
        (fun x => J S κ r ρ (referenceObserve S r x)) := by
  let : ∀ b : Background S, Nontrivial (Row S b) := fun b => by
    let : Nonempty (Fin (rows (Nodes.height (S b.1).upper))) := ⟨⟨0, hrows b.1⟩⟩
    exact inferInstance
  have hdim' (b : Background S) : Module.finrank F2 (Row S b) ≤ ℓ := by
    simpa only [Row, Block, Module.finrank_fin_fun] using hdim b.1
  have hevent : (fun x => J S κ r ρ (referenceObserve S r x)) =
      HeterogeneousAdviceFamily.J (table S κ) r ρ := by
    funext x
    exact reference_J S κ r ρ x
  rw [hevent]
  exact HeterogeneousAdviceFamily.J_probability_ge
    (backgroundLaw S outer backgrounds) (table S κ) r ℓ hdim' ρ η hη hρ hρ1 hconstants hmean

theorem reference_I_mass_ge (κ : ℝ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (r : Nat) (ρ : ℝ) :
    ρ * (referenceLaw S outer backgrounds r).probability
        (fun x => J S κ r ρ (referenceObserve S r x)) ≤
      (referenceLaw S outer backgrounds r).probability
        (fun x => I S κ r ρ (referenceObserve S r x)) := by
  have hJ : (fun x => J S κ r ρ (referenceObserve S r x)) =
      HeterogeneousAdviceFamily.J (table S κ) r ρ := by
    funext x
    exact reference_J S κ r ρ x
  have hI : (fun x => I S κ r ρ (referenceObserve S r x)) =
      HeterogeneousAdviceFamily.I (table S κ) r ρ := by
    funext x
    exact reference_I S κ r ρ x
  rw [hJ, hI]
  exact HeterogeneousAdviceFamily.I_probability_ge
    (backgroundLaw S outer backgrounds) (table S κ) r ρ

omit [Fintype O] in
theorem lower_I_implies_prediction (κ : ℝ) (r : Nat) (ρ : ℝ)
    (x : OriginalSample S r)
    (hL : HierarchicalAdviceExperiment.lowerEvent (S x.1) x.2.1 = true)
    (hI : I S κ r ρ (observe S r x) = true) :
    prediction S κ r ρ x = true :=
  HierarchicalAdviceExperiment.lower_I_implies_prediction (S x.1) κ r ρ x.2.1 x.2.2 hL hI

theorem prediction_difference (κ : ℝ) (hκ : 0 ≤ κ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))
    (ℓ : Nat) (hdim : ∀ o, rows (Nodes.height (S o).upper) ≤ ℓ)
    (r : Nat) (ρ η v : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ (backgroundLaw S outer backgrounds).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (table S κ b)))
    (hv : 0 ≤ v) (hsmall : v ≤ ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 16)
    (hvariation : ((originalLaw S outer r).pushforward (observe S r)).totalVariation
      ((referenceLaw S outer backgrounds r).pushforward (referenceObserve S r)) ≤ v) :
    κ * ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 4 ≤
      (originalLaw S outer r).probability (prediction S κ r ρ) -
      (κ * ρ / 4) * (originalLaw S outer r).probability
        (fun x => J S κ r ρ (observe S r x)) := by
  apply DependentPredictionDifference.of_original_usefulness outer
    (fun o => (S o).original) (fun o => HierarchicalAdviceExperiment.adviceLaw (S o) r)
    (referenceLaw S outer backgrounds r) (fun o => HierarchicalAdviceExperiment.coarse (S o))
    (referenceObserve S r) (fun o => HierarchicalAdviceExperiment.lowerEvent (S o))
    (I S κ r ρ) (J S κ r ρ) (prediction S κ r ρ)
    κ ρ ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) v
    hκ hρ.le hρ1.le (by positivity) hv hsmall
  · intro o z A hI
    exact HierarchicalAdviceExperiment.I_implies_mark (S o) κ r ρ z A hI
  · intro o x A hL hI
    exact HierarchicalAdviceExperiment.lower_I_implies_prediction (S o) κ r ρ x A hL hI
  · exact hvariation
  · exact reference_J_mass_ge S κ outer backgrounds hrows ℓ hdim r ρ η
      hη hρ hρ1 hconstants hmean
  · exact reference_I_mass_ge S κ outer backgrounds r ρ

end
end PerfectCompleteness.HierarchicalAdviceFamily


namespace PerfectCompleteness.HierarchicalOwnPrediction

noncomputable section

open scoped TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper lower : Nodes branch n) (lowerLevel : Nat)
  (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {Ω : Type*} (eval : Ω → NodeEmbedding.NodeH slots upper)
  (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
  (arrays : Arrays slots rows)

def input : OwnInputReference.Input slots rows upper lower W a :=
  OwnInputReference.readInput slots rows upper lower W a eval
    ((HiddenBucketBias.splitTape W Ω tape).2,
      OwnInputCanonicalQuery.exteriorOf slots rows upper lower arrays)

abbrev hidden := HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1

theorem response_eq_rightUpper (hne : upper ≠ lower)
    (hrows : BucketSampler.evaluate (rows (Nodes.height upper)) eval tape = arrays upper) :
    OwnInputReference.response slots rows upper lower W a σ
        (input slots upper lower W a eval tape arrays) (hidden slots upper W eval tape) =
      HierarchicalPrediction.rightUpper slots upper
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ lower hne a
        (NodeEmbedding.matrix arrays upper) := by
  rw [HierarchicalPrediction.rightUpper, HierarchicalMatrixTable.displayed_original]
  exact OwnInputCanonicalQuery.response_readInput_hidden_arrays
    slots rows upper lower hne W a σ eval tape arrays hrows

def correction
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    Module.Dual F2 (NodeEmbedding.RowSpace slots upper) :=
  RepresentativeMatrixTable.correctionFunctional (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper (HierarchicalMatrixTable.backgroundOf slots upper arrays))
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel
      (HierarchicalMatrixTable.backgroundOf slots upper arrays))
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel
      (HierarchicalMatrixTable.backgroundOf slots upper arrays))
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel
      (HierarchicalMatrixTable.backgroundOf slots upper arrays)) y.2

theorem correction_eq_of_background_eq (arrays' : Arrays slots rows)
    (hbackground : HierarchicalMatrixTable.backgroundOf slots upper arrays =
      HierarchicalMatrixTable.backgroundOf slots upper arrays')
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    correction slots upper lowerLevel arrays y =
      correction slots upper lowerLevel arrays' y := by
  exact congrArg (fun bg : HierarchicalMatrixTable.Background (rows := rows) slots upper =>
    RepresentativeMatrixTable.correctionFunctional (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper bg)
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel bg)
      (HierarchicalFrozenTables.sectionMap slots upper lowerLevel bg)
      (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel bg) y.2) hbackground

def nativeCorrection
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    Module.Dual F2 (NodeEmbedding.NodeH slots upper) :=
  (correction slots upper lowerLevel arrays y).comp (NodeEmbedding.embed slots upper)

def visibleOffset
    (known : HiddenBucketBias.VisibleDirection W → NodeEmbedding.NodeH slots upper)
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    Block rows upper :=
  HierarchicalTensorMatrix.visibleMatrix slots upper W known
    (correction slots upper lowerLevel arrays y) + y.1

theorem affinePrediction_eq_tensor
    (hrows : BucketSampler.evaluate (rows (Nodes.height upper)) eval tape = arrays upper)
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    HierarchicalPrediction.affinePrediction slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays)
        (NodeEmbedding.matrix arrays upper) y =
      visibleOffset slots upper lowerLevel W arrays
        (fun v => eval ((HiddenBucketBias.splitTape W Ω tape).2 v)) y +
      TensorBucketEvaluation.tensorOutput W (nativeCorrection slots upper lowerLevel arrays y)
        (hidden slots upper W eval tape) :=
  HierarchicalTensorMatrix.prediction_eq_visible_add_tensorOutput slots upper W eval tape
    arrays hrows (correction slots upper lowerLevel arrays y) y.1

theorem prediction_iff_own_tensor (hne : upper ≠ lower)
    (hrows : BucketSampler.evaluate (rows (Nodes.height upper)) eval tape = arrays upper)
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    HierarchicalPrediction.rightUpper slots upper
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ lower hne a
        (NodeEmbedding.matrix arrays upper) =
      HierarchicalPrediction.affinePrediction slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays)
        (NodeEmbedding.matrix arrays upper) y ↔
    OwnInputReference.response slots rows upper lower W a σ
        (input slots upper lower W a eval tape arrays) (hidden slots upper W eval tape) =
      visibleOffset slots upper lowerLevel W arrays
        (fun v => eval ((HiddenBucketBias.splitTape W Ω tape).2 v)) y +
      TensorBucketEvaluation.tensorOutput W (nativeCorrection slots upper lowerLevel arrays y)
        (hidden slots upper W eval tape) := by
  rw [response_eq_rightUpper slots upper lower W a σ eval tape arrays hne hrows,
    affinePrediction_eq_tensor slots upper lowerLevel W eval tape arrays hrows y]

end
end PerfectCompleteness.HierarchicalOwnPrediction


namespace PerfectCompleteness.HierarchicalUsefulFamily

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

abbrev Sample (Ω : O → Type*) := (o : O) × Ω o

def originalLaw (outer : FiniteDistribution O) : FiniteDistribution (Sample Ω) :=
  CompletionSoundness.sigmaLaw outer (fun o => (S o).original)

def jointEvent (upperEvent : (o : O) → Ω o → Bool) (x : Sample Ω) : Bool :=
  HierarchicalAdviceExperiment.lowerEvent (S x.1) x.2 && upperEvent x.1 x.2

def usefulEvent (κ : ℝ) (upperEvent : (o : O) → Ω o → Bool) (x : Sample Ω) : Bool :=
  upperEvent x.1 x.2 &&
    HierarchicalUsefulness.mark (S x.1).slots (S x.1).upper (S x.1).lowerLevel
      (S x.1).original (S x.1).arrays (HierarchicalAdviceExperiment.lowerEvent (S x.1)) κ
      (HierarchicalAdviceExperiment.coarse (S x.1) x.2)

omit [Fintype O] in
theorem usefulEvent_eq_table_defined (κ : ℝ)
    (upperEvent : (o : O) → Ω o → Bool) (x : Sample Ω) :
    usefulEvent S κ upperEvent x = (upperEvent x.1 x.2 &&
      (HierarchicalAdviceExperiment.table (S x.1) κ
        (HierarchicalAdviceExperiment.coarse (S x.1) x.2).1
        (HierarchicalAdviceExperiment.coarse (S x.1) x.2).2).isSome) := by
  simp only [HierarchicalAdviceExperiment.table, HierarchicalUsefulness.table_isSome]
  rfl

theorem joint_probability_eq_mean (outer : FiniteDistribution O)
    (upperEvent : (o : O) → Ω o → Bool) :
    (originalLaw S outer).probability (jointEvent S upperEvent) =
      outer.expectation (fun o => (S o).original.probability
        (fun x => HierarchicalAdviceExperiment.lowerEvent (S o) x && upperEvent o x)) :=
  CompletionSoundness.sigmaLaw_probability outer (fun o => (S o).original)
    (jointEvent S upperEvent)

theorem useful_probability_eq_mean (outer : FiniteDistribution O) (κ : ℝ)
    (upperEvent : (o : O) → Ω o → Bool) :
    (originalLaw S outer).probability (usefulEvent S κ upperEvent) =
      outer.expectation (fun o => (S o).original.probability
        (fun x => usefulEvent S κ upperEvent ⟨o, x⟩)) :=
  CompletionSoundness.sigmaLaw_probability outer (fun o => (S o).original)
    (usefulEvent S κ upperEvent)

theorem mean_useful_probability_ge_sub (outer : FiniteDistribution O)
    (upperEvent : (o : O) → Ω o → Bool) (κ c : ℝ) (hκ : 0 ≤ κ)
    (hjoint : c ≤ outer.expectation (fun o => (S o).original.probability
      (fun x => HierarchicalAdviceExperiment.lowerEvent (S o) x && upperEvent o x))) :
    c - κ ≤ outer.expectation (fun o => (S o).original.probability
      (fun x => usefulEvent S κ upperEvent ⟨o, x⟩)) := by
  have hpoint (o : O) :
      (S o).original.probability
          (fun x => HierarchicalAdviceExperiment.lowerEvent (S o) x && upperEvent o x) - κ ≤
        (S o).original.probability (fun x => usefulEvent S κ upperEvent ⟨o, x⟩) := by
    exact UsefulMark.useful_upper_ge_sub (S o).original
      (HierarchicalAdviceExperiment.coarse (S o))
      (HierarchicalAdviceExperiment.lowerEvent (S o)) (upperEvent o) κ
      ((S o).original.probability
        (fun x => HierarchicalAdviceExperiment.lowerEvent (S o) x && upperEvent o x))
      hκ le_rfl
  have hsum := Finset.sum_le_sum (fun o (_ : o ∈ (Finset.univ : Finset O)) =>
    mul_le_mul_of_nonneg_left (hpoint o) (outer.nonnegative o))
  have hintegrated :
      outer.expectation (fun o => (S o).original.probability
          (fun x => HierarchicalAdviceExperiment.lowerEvent (S o) x && upperEvent o x)) - κ ≤
        outer.expectation (fun o => (S o).original.probability
          (fun x => usefulEvent S κ upperEvent ⟨o, x⟩)) := by
    simpa only [FiniteDistribution.expectation, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, outer.normalized, one_mul] using hsum
  exact (sub_le_sub_right hjoint κ).trans hintegrated

theorem useful_probability_ge_sub (outer : FiniteDistribution O)
    (upperEvent : (o : O) → Ω o → Bool) (κ c : ℝ) (hκ : 0 ≤ κ)
    (hjoint : c ≤ (originalLaw S outer).probability (jointEvent S upperEvent)) :
    c - κ ≤ (originalLaw S outer).probability (usefulEvent S κ upperEvent) := by
  rw [useful_probability_eq_mean]
  exact mean_useful_probability_ge_sub S outer upperEvent κ c hκ
    (by simpa only [joint_probability_eq_mean] using hjoint)

theorem mean_useful_probability_ge_half (outer : FiniteDistribution O)
    (upperEvent : (o : O) → Ω o → Bool) (c : ℝ) (hc : 0 ≤ c)
    (hjoint : c ≤ outer.expectation (fun o => (S o).original.probability
      (fun x => HierarchicalAdviceExperiment.lowerEvent (S o) x && upperEvent o x))) :
    c / 2 ≤ outer.expectation (fun o => (S o).original.probability
      (fun x => usefulEvent S (c / 2) upperEvent ⟨o, x⟩)) := by
  have h := mean_useful_probability_ge_sub S outer upperEvent (c / 2) c
    (div_nonneg hc (by norm_num)) hjoint
  linarith

theorem useful_probability_ge_half (outer : FiniteDistribution O)
    (upperEvent : (o : O) → Ω o → Bool) (c : ℝ) (hc : 0 ≤ c)
    (hjoint : c ≤ (originalLaw S outer).probability (jointEvent S upperEvent)) :
    c / 2 ≤ (originalLaw S outer).probability (usefulEvent S (c / 2) upperEvent) := by
  have h := useful_probability_ge_sub S outer upperEvent (c / 2) c
    (div_nonneg hc (by norm_num)) hjoint
  linarith

end
end PerfectCompleteness.HierarchicalUsefulFamily

end OAI
