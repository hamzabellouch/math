import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Enum

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.FiniteSlotEncoding
open Finset Classical
variable {P : Type*}

theorem product_code {M : Type*} [CommMonoid M] (s : Finset P) (m : ℕ)
    (hs : s.card ≤ m) (W : P → M) :
    (∏ i : Fin m, (code s m i).elim 1 W)=∏ p ∈ s, W p := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Fin.prod_trunc]
  · calc
      _ = ∏ i : Fin s.card, W ((enum s) i).val := by
        apply prod_congr rfl
        intro i hi
        simp only [code,Fin.val_castAdd,dite_eq_left i.isLt,Option.elim_some]
      _ = ∏ p : s, W p.val := (enum s).prod_comp (fun p : s => W p.val)
      _ = _ := prod_coe_sort s W
  · intro j
    have hj : ¬s.card+j.val<s.card := by omega
    simp only [code,Fin.val_natAdd,dite_eq_right hj,Option.elim_none]
end OrdinaryCorrelations.FiniteSlotEncoding

end

end OAI
