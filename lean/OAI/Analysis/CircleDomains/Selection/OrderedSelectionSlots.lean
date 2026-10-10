import Mathlib.Data.Set.Countable
import Mathlib.Order.Monotone.Basic

namespace OAI

/-! A selection which adds at most one object per step has an enumeration in
its original order. Empty steps are retained as `none`, so every earlier
object occurs at a strictly earlier index. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

theorem exists_ordered_selection_slots {C : Type*} (A : ℕ → Set C)
    (hzero : A 0 = ∅) (hmono : Monotone A)
    (hsingle : ∀ n, (A (n + 1) \ A n).Subsingleton) :
    ∃ q : ℕ → Option C,
      (∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n) ∧
      (∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c) := by
  classical
  let q (n : ℕ) : Option C :=
    if h : (A (n + 1) \ A n).Nonempty then some h.choose else none
  have hq (n : ℕ) (c : C) : q n = some c ↔ c ∈ A (n + 1) \ A n := by
    dsimp only [q]
    split_ifs with h
    · constructor
      · intro hc
        have he := Option.some.inj hc
        exact he ▸ h.choose_spec
      · intro hc
        exact congrArg some (hsingle n h.choose_spec hc)
    · constructor
      · intro hc
        exact hc.elim
      · intro hc
        exact (h ⟨c, hc⟩).elim
  refine ⟨q, hq, ?_⟩
  intro n c
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      constructor
      · intro hc
        by_cases hprev : c ∈ A n
        · obtain ⟨k, hk, he⟩ := ih.mp hprev
          exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), he⟩
        · exact ⟨n, Nat.lt_succ_self n, (hq n c).mpr ⟨hc, hprev⟩⟩
      · rintro ⟨k, hk, he⟩
        by_cases hkn : k < n
        · exact hmono (Nat.le_succ n) (ih.mpr ⟨k, hkn, he⟩)
        · have hke : k = n := Nat.eq_of_lt_succ_of_not_lt hk hkn
          subst k
          exact ((hq n c).mp he).1

end CircleDomainRigidity

end

end OAI
