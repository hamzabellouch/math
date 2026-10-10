import OAI.Probability.SpanningForest.GraphFUSFLaw
import OAI.Probability.SpanningForest.EquivariantFUSFKernel

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.CanonicalFUSFLaw

theorem exists_kernel :
    ∃ μ : GraphCode → ProbabilityMeasure EdgeConfiguration,
      Measurable μ ∧
      (∀ G : GraphCode, GraphConnected G → GraphLocallyFinite G →
        HasFUSFLaw G (μ G : Measure EdgeConfiguration) id) ∧
      (∀ (σ : Equiv ℕ ℕ) (G : GraphCode),
        (μ G : Measure EdgeConfiguration).map (configurationRelabel σ) =
          (μ (relabelGraph σ G) : Measure EdgeConfiguration)) :=
  BorelFUSFKernel.exists_measurable_equivariant_fusf_kernel
    Problem336.exists_hasFUSFLaw

def probability (G : GraphCode) : ProbabilityMeasure EdgeConfiguration :=
  Classical.choose exists_kernel G

theorem measurable_probability : Measurable probability :=
  (Classical.choose_spec exists_kernel).1

theorem hasFUSFLaw (G : GraphCode) (hC : GraphConnected G)
    (hL : GraphLocallyFinite G) :
    HasFUSFLaw G (probability G : Measure EdgeConfiguration) id :=
  (Classical.choose_spec exists_kernel).2.1 G hC hL

theorem map_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) :
    (probability G : Measure EdgeConfiguration).map (configurationRelabel σ) =
      (probability (relabelGraph σ G) : Measure EdgeConfiguration) :=
  (Classical.choose_spec exists_kernel).2.2 σ G

def measure (G : GraphCode) : Measure EdgeConfiguration := probability G

instance (G : GraphCode) : IsProbabilityMeasure (measure G) := by
  unfold measure
  infer_instance

theorem hasLaw_of_hasFUSFLaw
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {G : GraphCode} (hC : GraphConnected G) (hL : GraphLocallyFinite G)
    {X : Ω → EdgeConfiguration} (hX : HasFUSFLaw G P X) :
    ProbabilityTheory.HasLaw X (measure G) P := by
  obtain ⟨H, hH⟩ := Problem336.exists_connectedExhaustion G hC hL
  refine ⟨(Measurable.of_eval hX.1).aemeasurable, ?_⟩
  have h := (hasFUSFLaw G hC hL).map_eq hX hH
  simpa only [Measure.map_id, measure] using h.symm

theorem isProbabilityMeasure_of_hasFUSFLaw
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {G : GraphCode} (hC : GraphConnected G) (hL : GraphLocallyFinite G)
    {X : Ω → EdgeConfiguration} (hX : HasFUSFLaw G P X) :
    IsProbabilityMeasure P :=
  (hasLaw_of_hasFUSFLaw hC hL hX).isProbabilityMeasure

end Problem336.CanonicalFUSFLaw

end

end OAI
