import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem measurable_relabel {d : ℕ} {α : Type*} [MeasurableSpace α]
    (g : TreeAut d) :
    Measurable (relabel g : (TreeVertex d → α) → (TreeVertex d → α)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem map_labelMeasure_relabel {d : ℕ} (g : TreeAut d) :
    Measure.map (relabel g) (labelMeasure d) = labelMeasure d := by
  exact Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective

theorem measurePreserving_relabel {d : ℕ} (g : TreeAut d) :
    MeasurePreserving (relabel g) (labelMeasure d) (labelMeasure d) :=
  ⟨measurable_relabel g, map_labelMeasure_relabel g⟩

end Problem367

end

end OAI
