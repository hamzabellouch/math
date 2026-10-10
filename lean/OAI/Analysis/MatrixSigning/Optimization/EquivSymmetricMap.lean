import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma equiv_symmetric_of_map_eq (L : E ≃L[ℝ] E) (F : E →L[ℝ] E)
    (he : L.toContinuousLinearMap = F) (hF : F.toLinearMap.IsSymmetric) :
    L.toLinearEquiv.toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ (L.toContinuousLinearMap u) v = inner ℝ u (L.toContinuousLinearMap v)
  rw [he]
  exact hF u v

end
end CurrentKS.KKT

end OAI
