import OAI.MeasureTheory.Falconer.Incidence.CubicIncidence
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Common point incidence of three original direction labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

def commonTripleRelation (E : Set (X × W)) : Set (X × (W × W × W)) :=
  {p | (p.1,p.2.1) ∈ E ∧ (p.1,p.2.2.1) ∈ E ∧ (p.1,p.2.2.2) ∈ E}

theorem commonTripleRelation_measurable (E : Set (X × W)) (hE : MeasurableSet E) :
    MeasurableSet (commonTripleRelation E) := by
  exact (hE.preimage (show Measurable (fun p : X × (W × W × W) => (p.1,p.2.1)) from by fun_prop)).inter
    ((hE.preimage (show Measurable (fun p : X × (W × W × W) => (p.1,p.2.2.1)) from by fun_prop)).inter
      (hE.preimage (show Measurable (fun p : X × (W × W × W) => (p.1,p.2.2.2)) from by fun_prop)))

omit [MeasurableSpace X] in
theorem commonTripleRelation_fiber (ν : Measure W) [SFinite ν]
    (E : Set (X × W)) (x : X) :
    (ν.prod (ν.prod ν)) (Prod.mk x ⁻¹' commonTripleRelation E) =
      (ν (Prod.mk x ⁻¹' E))^3 := by
  have he : Prod.mk x ⁻¹' commonTripleRelation E =
      (Prod.mk x ⁻¹' E) ×ˢ ((Prod.mk x ⁻¹' E) ×ˢ (Prod.mk x ⁻¹' E)) := rfl
  rw [he,Measure.prod_prod,Measure.prod_prod]
  ring

theorem common_triple_incidence_moment
    (μ : Measure X) (ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × W)) (hE : MeasurableSet E) :
    ((μ.prod ν) E)^3 ≤
      (μ.prod (ν.prod (ν.prod ν))) (commonTripleRelation E)*(μ univ)^2 := by
  have hf : Measurable (fun x : X => ν (Prod.mk x ⁻¹' E)) := measurable_measure_prodMk_left hE
  have hh := cubic_incidence_moment μ (fun x : X => ν (Prod.mk x ⁻¹' E)) hf.aemeasurable
  rw [Measure.prod_apply hE,Measure.prod_apply (commonTripleRelation_measurable E hE)]
  simpa only [commonTripleRelation_fiber] using hh

end Falconer

end OAI
