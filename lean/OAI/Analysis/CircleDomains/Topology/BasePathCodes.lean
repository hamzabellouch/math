import OAI.Analysis.CircleDomains.Modulus.PhysicalLengthCharacterization
import OAI.Analysis.CircleDomains.Topology.PathGates

namespace OAI

/-! The base-code space from the positive-law construction. The defining
relations are the actual path-hit and level incidences, with physical length,
finite deletions, optional tags, endpoint conditions and collar gates. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable (X Y : Type*) [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

structure PathCodeData where
  physicalDomain : Set Y
  quotientDomain : Set X
  domainEquiv : physicalDomain ≃ₜ quotientDomain
  basePoint : Y
  dust : Set X
  levels : ℕ → Set (UnitAddCircle × X)
  priorLaws : ℕ → Measure C(PathTime, X)
  priorDeletions : ℕ → ℕ → Finset X
  flagDeletions : ℕ → Finset X
  levelWeights : ℕ → X → ℝ≥0∞
  anchor : Set X
  target : X
  gateContours : ℕ → Set X
  gateSets : ℕ → Set X

variable {X Y}

def priorHitMass (μ : Measure C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  μ {η | (η, x) ∈ pathHitSet}

def AllowedTaggedPath (d : PathCodeData X Y) (dustMeasure : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) : Prop :=
  physicalDomainLength d.domainEquiv d.basePoint Γ.1 < ∞ ∧
  TagRules d.levels N Γ ∧
  ResidualConstraintFamily d.dust (fun _ => pathHitSet) d.priorDeletions d.priorLaws
    (fun i => priorHitMass (d.priorLaws i)) Γ ∧
  ResidualConstraintFamily d.dust d.levels (fun _ => d.flagDeletions)
    (fun _ => volume) d.levelWeights Γ ∧
  dustMeasure (residualImage d.dust Γ) = 0

def EndpointCode (d : PathCodeData X Y) (dustMeasure : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) : Prop :=
  AllowedTaggedPath d dustMeasure N Γ ∧
  (Γ.1 ⊥ ∈ d.anchor ∧ FirstArrival d.target Γ.1) ∧
  GateRules d.gateContours d.gateSets Γ.1

abbrev BasePathCode (d : PathCodeData X Y) :=
  {Γ : TaggedPath X // EndpointCode d 0 (fun _ _ => ∅) Γ}

variable [SecondCountableTopology X] [BorelSpace X]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurableSet_allowedTaggedPath (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i))
    [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (dustMeasure : Measure X) [SFinite dustMeasure]
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    MeasurableSet {Γ | AllowedTaggedPath d dustMeasure N Γ} := by
  unfold AllowedTaggedPath
  exact ((measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint).preimage
    measurable_fst).inter ((measurableSet_tagRules hH hN).inter
    ((measurableSet_residualConstraintFamily hB (fun _ => isClosed_pathHitSet)
      d.priorDeletions d.priorLaws hprior).inter
      ((measurableSet_residualConstraintFamily hB hH (fun _ => d.flagDeletions)
        (fun _ => volume) hlevel).inter (measurableSet_residualImageMass_zero hB dustMeasure))))

theorem measurableSet_endpointCode (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i))
    [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hC : ∀ i, IsClosed (d.gateContours i)) (hK : ∀ i, IsClosed (d.gateSets i))
    (dustMeasure : Measure X) [SFinite dustMeasure]
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    MeasurableSet {Γ | EndpointCode d dustMeasure N Γ} := by
  exact (measurableSet_allowedTaggedPath d hU hB hH hprior hlevel dustMeasure hN).inter
    ((measurableSet_endpointCodes hE d.target).inter
      ((measurableSet_gateRules hC hK).preimage measurable_fst))

theorem standardBorel_basePathCode [CompleteSpace X] (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i))
    [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hC : ∀ i, IsClosed (d.gateContours i)) (hK : ∀ i, IsClosed (d.gateSets i)) :
    StandardBorelSpace (BasePathCode d) :=
  (measurableSet_endpointCode d hU hB hH hprior hlevel hE hC hK 0
    (fun _ _ => MeasurableSet.empty)).standardBorel

def baseCodePhysicalPath (d : PathCodeData X Y) (Γ : BasePathCode d) :
    FinitePhysicalPath d.domainEquiv d.basePoint :=
  ⟨Γ.val.1, Γ.property.1.1⟩

end CircleDomainRigidity

end

end OAI
