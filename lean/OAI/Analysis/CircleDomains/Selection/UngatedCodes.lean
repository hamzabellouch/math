import OAI.Analysis.CircleDomains.Topology.BasePathCodes

namespace OAI

/-! A contour already contained in its allowed gate imposes no restriction.
This includes the ungated endpoint problems used in the transfinite recursion. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurableSet_endpointCode_of_vacuous_gates (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hgate : ∀ i, d.gateContours i ⊆ d.gateSets i)
    (dustMeasure : Measure X) [SFinite dustMeasure]
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    MeasurableSet {Γ | EndpointCode d dustMeasure N Γ} := by
  have hg (γ : C(PathTime, X)) : GateRules d.gateContours d.gateSets γ :=
    fun i _ ht => hgate i ht
  have heq : {Γ | EndpointCode d dustMeasure N Γ} =
      {Γ | AllowedTaggedPath d dustMeasure N Γ} ∩
      {Γ : TaggedPath X | Γ.1 ⊥ ∈ d.anchor ∧ FirstArrival d.target Γ.1} := by
    ext Γ
    simp only [EndpointCode, mem_ofPred_eq, mem_inter_iff, hg, and_true]
  rw [heq]
  exact (measurableSet_allowedTaggedPath d hU hB hH hprior hlevel dustMeasure hN).inter
    (measurableSet_endpointCodes hE d.target)

theorem standardBorel_basePathCode_of_vacuous_gates [CompleteSpace X]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hgate : ∀ i, d.gateContours i ⊆ d.gateSets i) :
    StandardBorelSpace (BasePathCode d) :=
  (measurableSet_endpointCode_of_vacuous_gates d hU hB hH hprior hlevel hE hgate 0
    (fun _ _ => MeasurableSet.empty)).standardBorel

end CircleDomainRigidity

end

end OAI
