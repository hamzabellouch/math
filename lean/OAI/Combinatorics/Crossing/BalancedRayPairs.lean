import OAI.Combinatorics.Crossing.FloorArithmetic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Fin

namespace OAI

namespace Zarankiewicz
open scoped Finset

def positiveRayIndices (r : ℕ) : Finset (Fin r) := Finset.univ.filter (fun i => i.val < r/2)
def negativeRayIndices (r : ℕ) : Finset (Fin r) := Finset.univ.filter (fun i => ¬ i.val < r/2)

def balancedRayPairs (r : ℕ) : Finset (Fin r × Fin r) :=
  ((positiveRayIndices r ×ˢ positiveRayIndices r).filter (fun p => p.1 < p.2)) ∪
    ((negativeRayIndices r ×ˢ negativeRayIndices r).filter (fun p => p.1 < p.2))

theorem mem_balancedRayPairs (r : ℕ) (i k : Fin r) :
    (i,k) ∈ balancedRayPairs r ↔ i < k ∧ (i.val < r/2 ↔ k.val < r/2) := by
  simp only [balancedRayPairs,positiveRayIndices,negativeRayIndices,Finset.mem_union,
    Finset.mem_filter,Finset.mem_product,Finset.mem_univ,true_and]
  tauto

theorem positiveRayIndices_card (r : ℕ) : (positiveRayIndices r).card=r/2 := by
  cases r with
  | zero => simp [positiveRayIndices]
  | succ r =>
    let c : Fin (r+1) := ⟨(r+1)/2,by omega⟩
    have he : positiveRayIndices (r+1)=Finset.Iio c := by
      ext i
      simp only [positiveRayIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
      rfl
    rw [he,Fin.card_Iio]

theorem negativeRayIndices_card (r : ℕ) : (negativeRayIndices r).card=r-r/2 := by
  have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin r => i.val < r/2)
  change (positiveRayIndices r).card+(negativeRayIndices r).card=Finset.univ.card at hh
  rw [positiveRayIndices_card,Finset.card_univ,Fintype.card_fin] at hh
  omega

theorem twice_choose_two (s : ℕ) : 2*s.choose 2=s*(s-1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right,Nat.add_sub_cancel]
    have hh : s*(s-1)+2*s=(s+1)*s := by
      cases s with
      | zero => simp
      | succ s => simp only [Nat.add_sub_cancel]; ring
    nlinarith

theorem balanced_choose_two (r : ℕ) : (r/2).choose 2+(r-r/2).choose 2=axisPairs r := by
  have hr : r=2*(r/2) ∨ r=2*(r/2)+1 := by omega
  rcases hr with hr | hr
  · generalize r/2=s at hr
    subst r
    rw [show 2*s-s=s by omega,axisPairs_even]
    have hh := twice_choose_two s
    omega
  · generalize r/2=s at hr
    subst r
    rw [show 2*s+1-s=s+1 by omega,axisPairs_odd,
      Nat.choose_succ_succ,Nat.choose_one_right]
    have hh := twice_choose_two s
    cases s with
    | zero => simp
    | succ s => simp only [Nat.add_sub_cancel] at hh; nlinarith

theorem balancedRayPairs_card (r : ℕ) : (balancedRayPairs r).card=axisPairs r := by
  have hd : Disjoint
      ((positiveRayIndices r ×ˢ positiveRayIndices r).filter (fun p => p.1 < p.2))
      ((negativeRayIndices r ×ˢ negativeRayIndices r).filter (fun p => p.1 < p.2)) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i,k⟩ hp hn
    simp only [Finset.mem_filter,Finset.mem_product,positiveRayIndices,negativeRayIndices,
      Finset.mem_univ,true_and] at hp hn
    exact hn.1.1 hp.1.1
  rw [balancedRayPairs,Finset.card_union_of_disjoint hd,Finset.card_product_filter_lt,
    Finset.card_product_filter_lt,positiveRayIndices_card,negativeRayIndices_card,balanced_choose_two]

end Zarankiewicz

end OAI
