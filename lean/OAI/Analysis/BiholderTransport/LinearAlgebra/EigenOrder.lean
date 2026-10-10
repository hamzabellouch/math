import Mathlib

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

def bilinearOperator (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

@[simp] lemma bilinearOperator_inner (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    inner ℝ (bilinearOperator B v) w=B v w :=
  InnerProductSpace.toDual_symm_apply

lemma bilinearOperator_symmetric {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v w:E, B v w=B w v) : (bilinearOperator B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (bilinearOperator B v) w=inner ℝ v (bilinearOperator B w)
  calc
    _=B v w := bilinearOperator_inner B v w
    _=B w v := hB v w
    _=inner ℝ (bilinearOperator B w) v := (bilinearOperator_inner B w v).symm
    _=inner ℝ v (bilinearOperator B w) := real_inner_comm _ _

lemma inverse_of_bilinear_pairing {B : E →L[ℝ] E →L[ℝ] ℝ} {R : E →L[ℝ] E}
    (hR : ∀ v w:E, B (R v) w=inner ℝ v w) (v:E) : bilinearOperator B (R v)=v := by
  exact ext_inner_right ℝ (fun w => by rw [bilinearOperator_inner,hR])
variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
lemma left_inverse_of_right_inverse {D R : E →L[ℝ] E}
    (hDR : ∀ v:E, D (R v)=v) (v:E) : R (D v)=v := by
  have hsurj : Function.Surjective D := fun w => ⟨R w,hDR w⟩
  have hinj : Function.Injective D := D.toLinearMap.injective_iff_surjective.mpr hsurj
  apply hinj
  exact hDR (D v)

end WeakMTWTransport

end

end OAI
