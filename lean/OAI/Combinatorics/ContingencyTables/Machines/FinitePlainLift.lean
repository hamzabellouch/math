import OAI.Combinatorics.ContingencyTables.Transport.RealKernelApproximation
import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # Exact moment and distance identities for the transversal embedding -/

namespace ContingencyTables.FinitePlainLift

open CommonBasesFPRAS RealKernelApproximation
open scoped BigOperators Classical

noncomputable section
variable {Γ : Type*} [Fintype Γ]

lemma sum_mul (gs : List (Γ × Γ)) (p : PlainIndex gs → ℝ)
    (g : ChainIndex gs → ℝ) :
    (∑ S,plainLift gs p S*g S)=∑ S : PlainIndex gs,p S*g S.val := by
  have h := Fintype.sum_subtype_add_sum_subtype (plainPredicate gs)
    (fun S => plainLift gs p S*g S)
  have ht (S : PlainIndex gs) : plainLift gs p S.val*g S.val=p S*g S.val := by
    rw [plainLift,dite_eq_left S.property]
  have hf (S : {S : ChainIndex gs // ¬plainPredicate gs S}) :
      plainLift gs p S.val*g S.val=0 := by
    rw [plainLift,dite_eq_right S.property,zero_mul]
  simp_rw [ht,hf,Finset.sum_const_zero,add_zero] at h
  exact h.symm

lemma distance_lift (gs : List (Γ × Γ)) (p q : PlainIndex gs → ℝ) :
    distance (plainLift gs p) (plainLift gs q)=distance p q := by
  have h := Fintype.sum_subtype_add_sum_subtype (plainPredicate gs)
    (fun S => |plainLift gs p S-plainLift gs q S|)
  have ht (S : PlainIndex gs) :
      |plainLift gs p S.val-plainLift gs q S.val|=|p S-q S| := by
    rw [plainLift,dite_eq_left S.property,plainLift,dite_eq_left S.property]
  have hf (S : {S : ChainIndex gs // ¬plainPredicate gs S}) :
      |plainLift gs p S.val-plainLift gs q S.val|=0 := by
    rw [plainLift,dite_eq_right S.property,plainLift,dite_eq_right S.property,sub_self,abs_zero]
  simp_rw [ht,hf,Finset.sum_const_zero,add_zero] at h
  unfold distance
  rw [h]

end
end ContingencyTables.FinitePlainLift

end OAI
