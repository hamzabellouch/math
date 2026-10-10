import Mathlib

namespace OAI

section
section
open scoped Classical
noncomputable section
namespace Coulomb

lemma exists_binary_order {n : ℕ} (p : Fin n → Fin 2) :
    ∃ m k : ℕ, ∃ e : Fin (m+k) ≃ Fin n,
      (∀ i : Fin m, p (e (Fin.castAdd k i))=0) ∧
      (∀ i : Fin k, p (e (Fin.natAdd m i))=1) := by
  let A := {i : Fin n // p i=0}
  let B := {i : Fin n // p i≠0}
  let m := Fintype.card A
  let k := Fintype.card B
  let eA : Fin m ≃ A := (Fintype.equivFin A).symm
  let eB : Fin k ≃ B := (Fintype.equivFin B).symm
  let e : Fin (m+k) ≃ Fin n := finSumFinEquiv.symm.trans ((eA.sumCongr eB).trans (Equiv.sumCompl (fun i => p i=0)))
  refine ⟨m,k,e,?_,?_⟩
  · intro i
    have he : e (Fin.castAdd k i) = (eA i).val := by
      simp only [e,Equiv.trans_apply,← finSumFinEquiv_apply_left,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inl]
      rfl
    rw [he]
    exact (eA i).property
  · intro i
    have he : e (Fin.natAdd m i) = (eB i).val := by
      simp only [e,Equiv.trans_apply,← finSumFinEquiv_apply_right,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inr]
      rfl
    rw [he]
    have h := (eB i).property
    exact Fin.eq_one_of_ne_zero _ h

end Coulomb
end

end
end

end OAI
