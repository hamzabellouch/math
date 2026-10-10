import OAI.Combinatorics.ContingencyTables.Dense.DenseMetropolisSemantics

namespace OAI

/-! # Exact bounded list slices of a finite Boolean word -/

namespace ContingencyTables.FiniteWordSlices

open FairBits

lemma slice_ofFn {N : ℕ} (bits : Fin N → Bool) (start count : ℕ)
    (h : start+count ≤ N) :
    ((List.ofFn bits).drop start).take count=
      List.ofFn (fun i : Fin count => bits ⟨start+i.val,by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]

abbrev Fields (p q k : ℕ) :=
  (Fin 1 → Bool) × ((Fin p → Bool) × (((Fin q → Bool) × (Fin q → Bool)) × (Fin k → Bool)))

def split (p q k : ℕ) : (Fin (1+(p+((q+q)+k))) → Bool) ≃ Fields p q k :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    ((splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((splitWordEquiv _ _).trans (Equiv.prodCongr (splitWordEquiv _ _) (Equiv.refl _))))))

lemma first_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop 1).take p=List.ofFn (split p q k bits).2.1 := by
  rw [slice_ofFn bits 1 p (by omega)]
  apply congrArg List.ofFn
  funext i
  rfl

lemma current_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop (1+p)).take q=List.ofFn (split p q k bits).2.2.1.1 := by
  rw [slice_ofFn bits (1+p) q (by omega)]
  apply congrArg List.ofFn
  funext i
  apply congrArg bits
  apply Fin.ext
  change 1+p+i.val=1+(p+i.val)
  omega

lemma target_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop (1+p+q)).take q=List.ofFn (split p q k bits).2.2.1.2 := by
  rw [slice_ofFn bits (1+p+q) q (by omega)]
  apply congrArg List.ofFn
  funext i
  apply congrArg bits
  apply Fin.ext
  change 1+p+q+i.val=1+(p+(q+i.val))
  omega

lemma coin_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop (1+p+q+q)).take k=List.ofFn (split p q k bits).2.2.2 := by
  rw [slice_ofFn bits (1+p+q+q) k (by omega)]
  apply congrArg List.ofFn
  funext i
  apply congrArg bits
  apply Fin.ext
  change 1+p+q+q+i.val=1+(p+((q+q)+i.val))
  omega

lemma holding_bit (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    (List.ofFn bits).getD 0 false=(split p q k bits).1 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp only [show 0 < 1+(p+((q+q)+k)) by omega,dite_true,Option.getD_some]
  rfl

end ContingencyTables.FiniteWordSlices

end OAI
