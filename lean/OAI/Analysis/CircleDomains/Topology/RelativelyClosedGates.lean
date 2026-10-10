import OAI.Analysis.CircleDomains.Selection.RecursiveReductionBase

namespace OAI

/-! Collar gates need be closed only on their closed contour. The preimage
of a closed target set under a map on the open domain has exactly this
property, even when its ambient closure reaches the boundary. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

 theorem isClosed_contour_gate {U C : Set X} (hC : IsClosed C) (hCU : C ⊆ U)
    {f : U → Y} (hf : Continuous f) {W : Set Y} (hW : IsClosed W) :
    IsClosed (C ∩ (Subtype.val '' (f ⁻¹' W))) := by
  let g : C → Y := fun x => f ⟨x.val, hCU x.property⟩
  have hg : Continuous g := hf.comp (continuous_subtype_val.subtype_mk _)
  have hs : IsClosed (Subtype.val '' (g ⁻¹' W)) :=
    hC.isClosedMap_subtype_val _ (hW.preimage hg)
  convert hs using 1
  ext x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    subst x
    exact ⟨⟨y.val, hx⟩, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, ⟨x.val, hCU x.property⟩, hx, rfl⟩

 theorem gateRule_inter_contour {C K : Set X} (γ : C(PathTime, X)) :
    GateRule C (C ∩ K) γ ↔ GateRule C K γ :=
  ⟨fun h t ht => (h t ht).2, fun h t ht => ⟨ht, h t ht⟩⟩

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

 theorem measurableSet_gateRules_of_inter_closed {C K : ℕ → Set X}
    (hC : ∀ n, IsClosed (C n)) (hCK : ∀ n, IsClosed (C n ∩ K n)) :
    MeasurableSet {γ | GateRules C K γ} := by
  have heq : {γ | GateRules C K γ} = {γ | GateRules C (fun n => C n ∩ K n) γ} := by
    ext γ
    exact forall_congr' fun n => (gateRule_inter_contour γ).symm
  rw [heq]
  exact measurableSet_gateRules hC hCK

variable [MeasurableSpace X]

 theorem codePathLaw_gates_of_inter_closed (d : PathCodeData X X)
    (hC : ∀ n, IsClosed (d.gateContours n))
    (hCK : ∀ n, IsClosed (d.gateContours n ∩ d.gateSets n))
    (P : ProbabilityMeasure (BasePathCode d)) :
    ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, X)),
      GateRules d.gateContours d.gateSets γ := by
  change ∀ᵐ γ ∂(P.map (codePath d) : Measure C(PathTime, X)), _
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_codePath d).aemeasurable
    (measurableSet_gateRules_of_inter_closed hC hCK)).mpr
  exact Eventually.of_forall fun Γ => Γ.property.2.2

 theorem IsSubarcLawReduction.code_gates_of_inter_closed
    (d : PathCodeData X X) (P : ProbabilityMeasure (BasePathCode d))
    {ν : ProbabilityMeasure C(PathTime, X)} (hred : IsSubarcLawReduction (codePathLaw d P) ν)
    (hC : ∀ n, IsClosed (d.gateContours n))
    (hCK : ∀ n, IsClosed (d.gateContours n ∩ d.gateSets n)) :
    ∀ᵐ γ ∂(ν : Measure C(PathTime, X)), GateRules d.gateContours d.gateSets γ := by
  have hμ := codePathLaw_gates_of_inter_closed d hC hCK P
  have hμ' : ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, X)),
      GateRules d.gateContours (fun n => d.gateContours n ∩ d.gateSets n) γ := by
    filter_upwards [hμ] with γ hγ
    exact fun n => (gateRule_inter_contour γ).mpr (hγ n)
  filter_upwards [hred.gates _ _ hC hCK hμ'] with γ hγ
  exact fun n => (gateRule_inter_contour γ).mp (hγ n)

variable [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]

 theorem standardBorel_basePathCode_of_inter_closed (d : PathCodeData X X)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hC : ∀ i, IsClosed (d.gateContours i))
    (hCK : ∀ i, IsClosed (d.gateContours i ∩ d.gateSets i)) :
    StandardBorelSpace (BasePathCode d) := by
  have hm : MeasurableSet {Γ | EndpointCode d 0 (fun _ _ => ∅) Γ} :=
    (measurableSet_allowedTaggedPath d hU hB hH hprior hlevel 0
      (fun _ _ => MeasurableSet.empty)).inter
      ((measurableSet_endpointCodes hE d.target).inter
        ((measurableSet_gateRules_of_inter_closed hC hCK).preimage measurable_fst))
  exact hm.standardBorel

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace CompactRecursiveReduction
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  {L : RecursiveCodeLaw base π Flags ω} {V : Set Sphere} {ε : ℝ≥0∞}
  (Q : CompactRecursiveReduction L V ε)

 theorem start_gate_of_inter_closed
    (hC : ∀ n, IsClosed (L.data.gateContours n))
    (hCK : ∀ n, IsClosed (L.data.gateContours n ∩ L.data.gateSets n))
    (n : ℕ) (hfront : frontier V ⊆ L.data.gateContours n) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs), γ.val ⊥ ∈ L.data.gateSets n := by
  have hgate := Q.reduction.code_gates_of_inter_closed L.data L.law hC hCK
  rw [ProbabilityMeasure.toMeasure_map] at hgate
  filter_upwards [ae_of_ae_map measurable_subtype_coe.aemeasurable hgate] with γ hγ
  exact hγ n ⊥ (hfront (Q.terminal γ.property).2.1)

 theorem physical_start_distance_of_inter_closed
    (hC : ∀ n, IsClosed (L.data.gateContours n))
    (hCK : ∀ n, IsClosed (L.data.gateContours n ∩ L.data.gateSets n))
    (n : ℕ) (hfront : frontier V ⊆ L.data.gateContours n)
    (f : base.quotientDomain → Sphere) (W : Set Sphere)
    (hgate : L.data.gateSets n = Subtype.val '' (f ⁻¹' closure W))
    (F₀ : ℂ → ℂ)
    (hF : ∀ x : base.quotientDomain, f x ∈ closure W →
      f x = (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint x.val)) : Sphere))
    (c : ℂ) (r : ℝ≥0) (δ : ℝ)
    (hgap : ∀ z : ℂ, (z : Sphere) ∈ closure W →
      δ ≤ Metric.infDist z (Metric.closedBall c (r : ℝ))) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs),
      δ ≤ Metric.infDist
        (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint (γ.val 0))))
        (Metric.closedBall c (r : ℝ)) := by
  filter_upwards [Q.start_gate_of_inter_closed hC hCK n hfront] with γ hγ
  rw [hgate] at hγ
  obtain ⟨x, hx, hxeq⟩ := hγ
  apply hgap
  change f x ∈ closure W at hx
  have heq := hF x hx
  rw [heq, hxeq] at hx
  exact hx

end CompactRecursiveReduction
end CircleDomainRigidity

end

end OAI
