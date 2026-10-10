import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.DistinctSlotStars

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrivateBankReserve

theorem exists_private_bank {m : ℕ} (ι : Fin 5 ↪ Fin m) (J : Finset (Fin m))
    (hreserve : 20 ≤ ((Finset.univ : Finset (Fin m)) \ (J ∪ orderedTrackAlphabet ι)).card) :
    ∃ e : (Fin 5 × Fin 5) ↪ Fin m,
      (∀ i, e (i,0)=ι i) ∧ ∀ i j : Fin 5, j≠0 → e (i,j) ∉ J := by
  classical
  let R := (Finset.univ : Finset (Fin m)) \ (J ∪ orderedTrackAlphabet ι)
  have hc : Fintype.card (Fin 5 × {j : Fin 5 // j≠0}) ≤ Fintype.card R := by
    rw [Fintype.card_prod,Fintype.card_fin]
    have hfour : Fintype.card {j : Fin 5 // j≠0}=4 := by decide
    rw [hfour]
    rw [Fintype.card_coe]
    exact hreserve
  obtain ⟨k⟩ : Nonempty ((Fin 5 × {j : Fin 5 // j≠0}) ↪ R) :=
    Function.Embedding.nonempty_of_card_le hc
  let f : Fin 5 × Fin 5 → Fin m := fun p => if h : p.2=0 then ι p.1 else (k (p.1,⟨p.2,h⟩)).val
  have hnot : ∀ i j hj, (k (i,⟨j,hj⟩)).val ∉ orderedTrackAlphabet ι := by
    intro i j hj
    exact fun hv => (Finset.mem_sdiff.mp (k (i,⟨j,hj⟩)).property).2 (Finset.mem_union_right _ hv)
  have hf : Function.Injective f := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he
    by_cases hj : j=0 <;> by_cases hj' : j'=0
    · subst j; subst j'
      have hi : ι i=ι i' := by simpa [f] using he
      exact Prod.ext (ι.injective hi) rfl
    · subst j
      have he' : ι i=(k (i',⟨j',hj'⟩)).val := by simpa [f,hj'] using he
      exact False.elim (hnot i' j' hj' (he' ▸ orderedTrackAlphabet_mem ι i))
    · subst j'
      have he' : (k (i,⟨j,hj⟩)).val=ι i' := by simpa [f,hj] using he
      exact False.elim (hnot i j hj (he'.symm ▸ orderedTrackAlphabet_mem ι i'))
    · have he' : k (i,⟨j,hj⟩)=k (i',⟨j',hj'⟩) := Subtype.ext (by simpa [f,hj,hj'] using he)
      have hx := k.injective he'
      have hi : i=i' := congrArg (fun p : Fin 5 × {j : Fin 5 // j≠0} => p.1) hx
      have hjj : j=j' := congrArg (fun p : Fin 5 × {j : Fin 5 // j≠0} => p.2.val) hx
      exact Prod.ext hi hjj
  refine ⟨⟨f,hf⟩,?_,?_⟩
  · intro i; simp [f]
  · intro i j hj
    change f (i,j) ∉ J
    simp only [f,hj,dite_false]
    exact fun hv => (Finset.mem_sdiff.mp (k (i,⟨j,hj⟩)).property).2 (Finset.mem_union_left _ hv)

end PrivateBankReserve

end SimpleAmenable
end
end

end OAI
