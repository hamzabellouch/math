import OAI.Probability.FirstPassage.ProbabilityFoundations

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

def shiftEdge (a : Vertex) (e : Edge) : Edge := (a+e.1,e.2)

theorem shiftEdge_injective (a : Vertex) : Function.Injective (shiftEdge a) := by
  intro e f h
  simpa [shiftEdge, Prod.ext_iff] using h

theorem step_edge_translate (a p : Vertex) (d : Step) :
    d.edge (a+p) = shiftEdge a (d.edge p) := by
  cases d <;> simp [Step.edge, shiftEdge, add_assoc]

theorem pathCost_translate (w : Edge → ℝ) (a p : Vertex) (ds : List Step) :
    pathCost (fun e => w (shiftEdge a e)) p ds = pathCost w (a+p) ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost, step_edge_translate, ih, add_assoc]

theorem passageTime_translate (w : Edge → ℝ) (a p q : Vertex) :
    passageTime (fun e => w (shiftEdge a e)) p q = passageTime w (a+p) (a+q) := by
  unfold passageTime
  congr 1
  ext t
  simp only [mem_ofPred_eq, pathCost_translate, add_assoc, add_left_cancel_iff]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.translate (h : ExponentialEnvironment P τ) (a : Vertex) :
    ExponentialEnvironment P (fun e => τ (shiftEdge a e)) where
  probability := h.probability
  measurable := fun _ => h.measurable _
  independent := h.independent.precomp (shiftEdge_injective a)
  marginal := fun _ => h.marginal _

theorem ExponentialEnvironment.jointLaw (h : ExponentialEnvironment P τ) :
    Measure.map (fun ω e => τ e ω) P = exponentialProductLaw := by
  rw [h.independent.map_fun_eq_infinitePi_map h.measurable]
  simp only [h.marginal, exponentialProductLaw]

theorem translated_event_probability (h : ExponentialEnvironment P τ) (a : Vertex)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) :
    P {ω | (fun e => τ (shiftEdge a e) ω) ∈ A} =
      P {ω | (fun e => τ e ω) ∈ A} := by
  have h1 := (h.translate a).jointLaw
  have h2 := h.jointLaw
  have he := congrArg (fun Q : Measure (Edge → ℝ) => Q A) (h1.trans h2.symm)
  rw [Measure.map_apply (Measurable.of_eval (fun e => h.measurable _)) hA,
    Measure.map_apply (Measurable.of_eval h.measurable) hA] at he
  exact he

end PlanarFPP

end OAI
