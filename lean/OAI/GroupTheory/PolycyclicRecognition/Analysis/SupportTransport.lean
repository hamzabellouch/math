import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportNorm

namespace OAI

/-! # Transporting support data to the chosen height coordinates -/

namespace PolycyclicRecognition.SupportDatum

variable {V W I B : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [Fintype I] [Fintype B]

/-- Change the linear coordinates on height, retaining the word multiplicities. -/
def transport (D : PolycyclicRecognition.SupportDatum V I B) (e : V ≃ₗ[ℝ] W) :
    PolycyclicRecognition.SupportDatum W I B where
  weight i := (D.weight i).comp e.symm.toLinearMap
  multiplicity := D.multiplicity
  positive := D.positive
  balanced b w := D.balanced b (e.symm w)
  separates w h := by
    have hw := D.separates (e.symm w) h
    simpa only [e.apply_symm_apply, map_zero] using congrArg e hw

@[simp] theorem transport_weight_apply (D : PolycyclicRecognition.SupportDatum V I B)
    (e : V ≃ₗ[ℝ] W) (i : I) (w : W) :
    (D.transport e).weight i w = D.weight i (e.symm w) := rfl

end PolycyclicRecognition.SupportDatum

end OAI
