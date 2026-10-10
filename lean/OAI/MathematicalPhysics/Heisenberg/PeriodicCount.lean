import OAI.MathematicalPhysics.Heisenberg.MeshMatrixSurface

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface

lemma periodic_count (k Q : ℕ) (P : ℕ → Prop) :
    (Finset.univ.filter (fun j : Fin (k*Q)=>P (j.val%Q))).card=
      k*(Finset.univ.filter (fun j : Fin Q=>P j.val)).card := by
  simp only [Finset.card_filter]
  have hh:=Fintype.sum_equiv (finProdFinEquiv (m:=k) (n:=Q))
    (fun j : Fin k × Fin Q=>if P j.2.val then (1:ℕ) else 0)
    (fun j : Fin (k*Q)=>if P (j.val%Q) then (1:ℕ) else 0)
    (fun j=>by simp [finProdFinEquiv,Nat.mod_eq_of_lt j.2.isLt])
  rw [←hh]
  rw [Fintype.sum_prod_type]
  trans ∑ _ : Fin k,∑ j : Fin Q,if P j.val then (1:ℕ) else 0
  · congr! 20
  · simp

lemma truncated_count (q Q : ℕ) (hq : q≤Q) (P : ℕ → Prop) :
    (Finset.univ.filter (fun j : Fin Q=>j.val<q ∧ P j.val)).card=
      ((Finset.range q).filter P).card := by
  apply Finset.card_nbij (fun j : Fin Q=>j.val)
  · intro j hj
    simpa only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_range] using hj
  · intro i _ j _ h; exact Fin.ext h
  · intro j hj
    have h:=Finset.mem_filter.mp hj
    exact ⟨⟨j,lt_of_lt_of_le (Finset.mem_range.mp h.1) hq⟩,by simpa using h,rfl⟩

lemma periodic_truncated_count (k q Q : ℕ) (hq : q≤Q) (P : ℕ → Prop) :
    (Finset.univ.filter (fun j : Fin (k*Q)=>j.val%Q<q ∧ P (j.val%Q))).card=
      k*((Finset.range q).filter P).card := by
  trans k*(Finset.univ.filter (fun j : Fin Q=>j.val<q ∧ P j.val)).card
  · convert periodic_count k Q (fun j=>j<q ∧ P j) using 1 <;> congr! 10
  · rw [truncated_count q Q hq]

end Heisenberg.Surface
end
end

end OAI
