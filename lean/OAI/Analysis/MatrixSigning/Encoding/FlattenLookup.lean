import Mathlib
import OAI.Analysis.MatrixSigning.Realization.ArrayRealization

namespace OAI

section

namespace CurrentKS.Realization

lemma getD_flatten_ofFn {α : Type*} {n m : ℕ} (rows : Fin n → List α)
    (hl : ∀ i,(rows i).length=m) (i : Fin n) (j : ℕ) (hj : j < m) (d : α) :
    (List.ofFn rows).flatten.getD (i.val*m+j) d=(rows i).getD j d := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ,List.flatten_cons]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add]
      exact List.getD_append _ _ _ _ (by simpa only [hl] using hj)
    · rw [List.getD_append_right _ _ _ _ (by rw [hl];simp only [Fin.val_succ,Nat.add_mul,Nat.one_mul];omega)]
      simp only [hl,Fin.val_succ]
      have he : (k.val+1)*m+j-m=k.val*m+j := by simp only [Nat.add_mul,Nat.one_mul];omega
      rw [he]
      exact ih (fun i => rows i.succ) (fun i => hl i.succ) k

end CurrentKS.Realization

end

end OAI
