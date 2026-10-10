import OAI.Analysis.CircleDomains.Topology.SubarcIntersectionCount
import OAI.Analysis.CircleDomains.Probability.CodePathLaws
import OAI.Analysis.CircleDomains.Topology.PathGates
import OAI.Analysis.CircleDomains.Topology.TerminalArcSet

namespace OAI

/-! The original endpoint law's prescribed closed gates survive measurable subarc
selection and compact conditioning. In particular the localized arc starts satisfy
the very same collar gate used by the positive-law construction. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

 theorem GateRule.of_range_subset {C K : Set X} {γ α : C(PathTime, X)}
    (hγ : GateRule C K γ) (hsub : range α ⊆ range γ) : GateRule C K α := by
  intro t ht
  obtain ⟨u, hu⟩ := hsub (mem_range_self t)
  rw [← hu] at ht ⊢
  exact hγ u ht

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

 theorem IsSubarcLawReduction.gates
    {μ ν : ProbabilityMeasure C(PathTime, X)} (hred : IsSubarcLawReduction μ ν)
    (C K : ℕ → Set X) (hC : ∀ n, IsClosed (C n)) (hK : ∀ n, IsClosed (K n))
    (hμ : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), GateRules C K γ) :
    ∀ᵐ γ ∂(ν : Measure C(PathTime, X)), GateRules C K γ := by
  obtain ⟨f, hf, hs, hν⟩ := hred
  have hsel : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), GateRules C K (f γ) := by
    filter_upwards [hμ, hs] with γ hγ hsub
    exact fun n => (hγ n).of_range_subset hsub
  have hmap : ∀ᵐ γ ∂(μ.map f : Measure C(PathTime, X)), GateRules C K γ := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff hf (measurableSet_gateRules hC hK)).mpr hsel
  exact (Measure.absolutelyContinuous_of_le_smul hν).ae_le hmap

variable [MeasurableSpace X]

 theorem codePathLaw_gates (d : PathCodeData X Y)
    (hC : ∀ n, IsClosed (d.gateContours n)) (hK : ∀ n, IsClosed (d.gateSets n))
    (P : ProbabilityMeasure (BasePathCode d)) :
    ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, X)),
      GateRules d.gateContours d.gateSets γ := by
  change ∀ᵐ γ ∂(P.map (codePath d) : Measure C(PathTime, X)), _
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_codePath d).aemeasurable
    (measurableSet_gateRules hC hK)).mpr
  exact Eventually.of_forall fun Γ => Γ.property.2.2

 theorem IsSubarcLawReduction.code_gates
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    {ν : ProbabilityMeasure C(PathTime, X)} (hred : IsSubarcLawReduction (codePathLaw d P) ν)
    (hC : ∀ n, IsClosed (d.gateContours n)) (hK : ∀ n, IsClosed (d.gateSets n)) :
    ∀ᵐ γ ∂(ν : Measure C(PathTime, X)), GateRules d.gateContours d.gateSets γ :=
  hred.gates d.gateContours d.gateSets hC hK (codePathLaw_gates d hC hK P)

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem IsSubarcLawReduction.terminal_start_gate
    (d : PathCodeData Sphere Sphere) (P : ProbabilityMeasure (BasePathCode d))
    {ν : ProbabilityMeasure C(PathTime, Sphere)} (hred : IsSubarcLawReduction (codePathLaw d P) ν)
    (hC : ∀ n, IsClosed (d.gateContours n)) (hK : ∀ n, IsClosed (d.gateSets n))
    (n : ℕ) (V : Set Sphere) (hfront : frontier V ⊆ d.gateContours n)
    (hterminal : ∀ᵐ γ ∂(ν : Measure C(PathTime, Sphere)), γ ∈ terminalArcSet V d.target) :
    ∀ᵐ γ ∂(ν : Measure C(PathTime, Sphere)), γ ⊥ ∈ d.gateSets n := by
  filter_upwards [hred.code_gates d P hC hK, hterminal] with γ hγ ht
  exact hγ n ⊥ (hfront ht.2.1)

end CircleDomainRigidity

end

end OAI
