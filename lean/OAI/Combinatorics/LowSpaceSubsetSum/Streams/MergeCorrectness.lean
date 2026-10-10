import OAI.Combinatorics.LowSpaceSubsetSum.Streams.RowMerge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.AddSub

namespace OAI

/-!
# Complete and stopped tournament merges

The multiset view counts every row occurrence, even when all item fields
coincide. Each successful advance removes exactly the reported occurrence.
A sufficiently long trace therefore enumerates the whole product stream;
the potential also bounds every stopped execution's number of advances.
-/

namespace LowSpaceSubsetSum
namespace RowMerge

universe u v

variable {α : Type u} {σ : Type v} {d : ℕ}

def bag (view : σ → List α) (t : Tournament.Tree (Front d α σ) d) : Multiset α :=
  ∑ p : Path d, (remaining view t p : Multiset α)

theorem bag_card (view : σ → List α) (t : Tournament.Tree (Front d α σ) d) :
    (bag view t).card = potential view t := by simp [bag, potential]

theorem replacement_bag (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t)
    {x : Front d α σ} (hx : Tournament.winner t = some x) :
    bag view t = {x.value} + bag view (Tournament.replace (fun y => key y.value) t
      x.row (front read x.row x.after)) := by
  have hrow := winner_at_own_row key t ht halign hx
  let t' := Tournament.replace (fun y => key y.value) t x.row (front read x.row x.after)
  have hpoint (p : Path d) : (remaining view t p : Multiset α) =
      (remaining view t' p : Multiset α) + if p = x.row then {x.value} else 0 := by
    have hnew := replace_remaining key read view hread t x p
    change remaining view t' p = _ at hnew
    by_cases hp : p = x.row
    · subst p
      rw [ite_eq_left rfl] at hnew
      rw [hnew]
      simp only [remaining, hrow, ↓reduceIte]
      change x.value ::ₘ (view x.after : Multiset α) = (view x.after : Multiset α) + {x.value}
      rw [← Multiset.singleton_add, add_comm]
    · rw [ite_eq_right (Ne.symm hp)] at hnew
      rw [hnew, ite_eq_right hp, add_zero]
  unfold bag
  rw [show (∑ p : Path d, (remaining view t p : Multiset α)) =
      ∑ p : Path d, ((remaining view t' p : Multiset α) + if p = x.row then {x.value} else 0)
      from Finset.sum_congr rfl (fun p _ => hpoint p)]
  simp [Finset.sum_add_distrib, t', add_comm]

theorem bag_eq_zero_of_winner_none (key : α → ℤ)
    (view : σ → List α) (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (hn : Tournament.winner t = none) :
    bag view t = 0 := by
  have hc := (Tournament.winner_none_iff (fun y => key y.value) t ht).mp hn
  have hlookup (p : Path d) : Tournament.lookup t p = none := by
    cases h : Tournament.lookup t p with
    | none => rfl
    | some x =>
      have hm := (Tournament.mem_candidates_iff t x).mpr ⟨p, h⟩
      simp [hc] at hm
  simp [bag, remaining, hlookup]

/-- Analysis view of repeated advances. The program can stop between them. -/
def trace (key : α → ℤ) (read : σ → Option (α × σ)) :
    ℕ → Tournament.Tree (Front d α σ) d → List α
  | 0, _ => []
  | k + 1, t => match advance key read t with
    | none => []
    | some (a, t') => a :: trace key read k t'

theorem trace_complete (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view) (k : ℕ)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t)
    (hk : potential view t ≤ k) : (trace key read k t : Multiset α) = bag view t := by
  induction k generalizing t with
  | zero =>
    have hz : (bag view t).card = 0 := by rw [bag_card]; omega
    simpa [trace] using (Multiset.card_eq_zero.mp hz).symm
  | succ k ih =>
    cases hw : Tournament.winner t with
    | none =>
      have hb := bag_eq_zero_of_winner_none key view t ht hw
      simp [trace, advance, hw, hb]
    | some x =>
      let t' := Tournament.replace (fun y => key y.value) t x.row (front read x.row x.after)
      have ha : advance key read t = some (x.value, t') := by simp [advance, hw, t']
      have ht' := advance_valid key read t ht ha
      have halign' := advance_aligned key read t halign ha
      have hdec := replacement_consumes_one key read view hread t ht halign hw
      change potential view t' + 1 = potential view t at hdec
      have hk' : potential view t' ≤ k := by omega
      have hbag := replacement_bag key read view hread t ht halign hw
      change bag view t = {x.value} + bag view t' at hbag
      rw [trace, ha]
      change x.value ::ₘ (trace key read k t' : Multiset α) = bag view t
      rw [ih t' ht' halign' hk', hbag]
      simp

theorem trace_length_le (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view) (k : ℕ)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t) :
    (trace key read k t).length ≤ potential view t := by
  induction k generalizing t with
  | zero => simp [trace]
  | succ k ih =>
    cases hw : Tournament.winner t with
    | none => simp [trace, advance, hw]
    | some x =>
      let t' := Tournament.replace (fun y => key y.value) t x.row (front read x.row x.after)
      have ha : advance key read t = some (x.value, t') := by simp [advance, hw, t']
      have ht' := advance_valid key read t ht ha
      have halign' := advance_aligned key read t halign ha
      have hdec := replacement_consumes_one key read view hread t ht halign hw
      have hlen := ih t' ht' halign'
      rw [trace, ha, List.length_cons]
      change potential view t' + 1 = potential view t at hdec
      omega

end RowMerge
end LowSpaceSubsetSum

end OAI
