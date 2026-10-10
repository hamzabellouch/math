import OAI.Computability.PerfectCompleteness.Foundations.OddLists

namespace OAI

section

namespace PerfectCompleteness.OddLists

open scoped BigOperators Classical

noncomputable section

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

private theorem parityPushforward_comp (π : A → B) (ρ : B → C) (L : Finset A) :
    parityPushforward ρ (parityPushforward π L) =
      parityPushforward (ρ ∘ π) L := by
  let f : A → ZMod 2 := fun a => if a ∈ L then 1 else 0
  have hf : support f = L := by
    ext a
    by_cases ha : a ∈ L <;> simp [mem_support, f, ha]
  rw [← hf, parityPushforward_support, parityPushforward_support,
    parityPushforward_support]
  apply congrArg (fun g : C → ZMod 2 => support g)
  funext c
  calc
    (∑ b, if ρ b = c then ∑ a, if π a = b then f a else 0 else 0) =
        ∑ b, ∑ a, if ρ b = c then (if π a = b then f a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : ρ b = c <;> simp only [hb, ite_true, ite_false, Finset.sum_const_zero]
    _ = ∑ a, ∑ b, if ρ b = c then (if π a = b then f a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ a, if (ρ ∘ π) a = c then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (π a)]
      · simp only [Function.comp_apply, ite_true]
      · intro b _ hb
        simp only [ite_eq_right (Ne.symm hb), ite_self]
      · intro h
        exact (h (Finset.mem_univ _)).elim

namespace OddList

theorem map_comp {s : Nat} (π : A → B) (ρ : B → C) (L : OddList s A) :
    map ρ (map π L) = map (ρ ∘ π) L := by
  apply Subtype.ext
  exact parityPushforward_comp π ρ L.val

theorem map_commutes {D : Type*} [Fintype D] [DecidableEq D] {s : Nat}
    (π : A → B) (α : A → C) (β : B → D) (ρ : C → D)
    (h : ∀ a, ρ (α a) = β (π a))
    (L : OddList s A) (R : OddList s B) (hnative : map π L = R) :
    map ρ (map α L) = map β R := by
  rw [map_comp α ρ L, show ρ ∘ α = β ∘ π from funext h,
    ← map_comp π β L, hnative]

end OddList

end
end PerfectCompleteness.OddLists

end

end OAI
