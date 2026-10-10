import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.InnerRight

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

lemma sandwich_sub (A U V : H d) : sandwich A (U-V) = sandwich A U - sandwich A V := by
  apply Subtype.ext
  change (A : Mat d) * ((U : Mat d)-(V : Mat d)) * (A : Mat d) = _
  simp only [mul_sub, sub_mul]
  rfl

lemma invH_involutive (X : H d) (hX : X ∈ pd d) : invH (invH X) = X := by
  apply Subtype.ext
  exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit)

lemma sandwich_inverse_cancel' (X P : H d) (hX : X ∈ pd d) :
    sandwich (invH X) (sandwich X P) = P := by
  simpa only [invH_involutive X hX] using sandwich_inverse_cancel (invH X) P hX.inv

def sandwichCLM (A : H d) : H d →L[ℝ] H d :=
  ({ toFun := sandwich A
     map_add' := sandwich_add A
     map_smul' := fun r U => sandwich_smul r A U } : H d →ₗ[ℝ] H d).toContinuousLinearMap

@[simp] lemma sandwichCLM_apply (A U : H d) : sandwichCLM A U = sandwich A U := rfl

lemma psd_pointed (A : H d) (hA : A ∈ psdCone d) (hnA : -A ∈ psdCone d) : A = 0 := by
  have h0 := (mem_psd_iff_nonneg A).mp hA
  have h1 := (mem_psd_iff_nonneg (-A)).mp hnA
  exact le_antisymm (neg_nonneg.mp h1) h0

end
end CurrentKS.Hermitian

end OAI
