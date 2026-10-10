import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-! # Exact pair counting by the two population labels -/

namespace Ostmann

open scoped BigOperators Classical

def filteredPairFiberEquiv {A B C D : Type*} (f : A → C) (g : B → D)
    (R : C → D → Prop) :
    {z : A × B // R (f z.1) (g z.2)} ≃
      Σ q : {z : C × D // R z.1 z.2},
        {x : A // f x = q.1.1} × {y : B // g y = q.1.2} where
  toFun z := ⟨⟨(f z.1.1, g z.1.2), z.2⟩, ⟨z.1.1, rfl⟩, ⟨z.1.2, rfl⟩⟩
  invFun z := ⟨(z.2.1.1, z.2.2.1), by rw [z.2.1.2, z.2.2.2]; exact z.1.2⟩
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨⟨c, d⟩, h⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩
    dsimp only at hx hy
    subst c d
    rfl

theorem filteredPair_card {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → C) (g : B → D) (R : C → D → Prop) :
    Fintype.card {z : A × B // R (f z.1) (g z.2)} =
      ∑ q : {z : C × D // R z.1 z.2},
        Fintype.card {x : A // f x = q.1.1} * Fintype.card {y : B // g y = q.1.2} := by
  rw [Fintype.card_congr (filteredPairFiberEquiv f g R), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro q _
  exact Fintype.card_prod _ _

theorem filteredPair_card_le {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → C) (g : B → D) (R : C → D → Prop) (K H : ℝ)
    (hK : 0 ≤ K)
    (hlabels : (Fintype.card {z : C × D // R z.1 z.2} : ℝ) ≤ H)
    (hpop : ∀ q : {z : C × D // R z.1 z.2},
      (Fintype.card {x : A // f x = q.1.1} : ℝ) *
        Fintype.card {y : B // g y = q.1.2} ≤ K) :
    (Fintype.card {z : A × B // R (f z.1) (g z.2)} : ℝ) ≤ H * K := by
  rw [filteredPair_card f g R, Nat.cast_sum]
  calc
    _ ≤ ∑ _q : {z : C × D // R z.1 z.2}, K := by
      apply Finset.sum_le_sum
      intro q _
      simpa only [Nat.cast_mul] using hpop q
    _ = (Fintype.card {z : C × D // R z.1 z.2} : ℝ) * K := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hlabels hK

/-- If the total pair count exceeds the label count times K, a compatible
pair of labels has population product greater than K. -/
theorem exists_large_pair_fiber {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → C) (g : B → D) (R : C → D → Prop) (K : ℝ) (hK : 0 ≤ K)
    (hlarge : (Fintype.card {z : C × D // R z.1 z.2} : ℝ) * K <
      (Fintype.card {z : A × B // R (f z.1) (g z.2)} : ℝ)) :
    ∃ q : {z : C × D // R z.1 z.2}, K <
      (Fintype.card {x : A // f x = q.1.1} : ℝ) * Fintype.card {y : B // g y = q.1.2} := by
  by_contra! hn
  have hb := filteredPair_card_le f g R K _ hK le_rfl hn
  exact (not_lt_of_ge hb) hlarge

def finsetFiberEquiv {A B : Type*} [DecidableEq A] [DecidableEq B] (S : Finset A) (f : A → B) (b : B) :
    {x : S // f x = b} ≃ {x : A // x ∈ S.filter (fun x => f x = b)} where
  toFun x := ⟨x.1, Finset.mem_filter.mpr ⟨x.1.property, x.2⟩⟩
  invFun x := ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finset_fiber_card {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (b : B) :
    Fintype.card {x : S // f x = b} = (S.filter fun x => f x = b).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (finsetFiberEquiv S f b)

end Ostmann

end OAI
