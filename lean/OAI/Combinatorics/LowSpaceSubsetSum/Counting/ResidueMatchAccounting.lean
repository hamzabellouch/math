import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MatchPotential
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.FilteredRow
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ResidueFilters

namespace OAI

/-!
# Every potential Cartesian match is charged to one residue iteration

The calculation counts list occurrences, including repetitions. Summing the
full potential over all residues counts every Cartesian pair exactly once.
The complementary right-hand residue loop is the same finite sum after an
explicit involutive reindexing.
-/

namespace LowSpaceSubsetSum
namespace ResidueMatchAccounting

variable {α β : Type*} {q : ℕ}

theorem direct_match_iff (hq : 0 < q) (x y : ℤ) (z : Fin q) :
    x % (q : ℤ) = ((z.val : ℤ) - y) % q ↔ normalizedResidue hq (x + y) = z := by
  have hz : (z.val : ℤ) % q = z.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast z.isLt)
  rw [← FilteredRow.eligible (q : ℤ) z.val y x, add_comm y x, hz]
  exact (normalizedResidue_eq_iff hq (x + y) z).symm

theorem sum_filter_lengths (label : β → Fin q) (ys : List β) :
    (∑ z : Fin q, (ys.filter (fun y => decide (label y = z))).length) = ys.length := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    have hpoint (z : Fin q) :
        ((y :: ys).filter (fun y => decide (label y = z))).length =
          (if label y = z then 1 else 0) + (ys.filter (fun y => decide (label y = z))).length := by
      by_cases h : label y = z <;> simp [h, Nat.add_comm]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, ih]
    simp [Nat.add_comm]

theorem sum_potential (hq : 0 < q) (wx : α → ℤ) (wy : β → ℤ) (xs : List α) (ys : List β) :
    (∑ z : Fin q, MatchPotential.count (fun x => wx x % (q : ℤ))
      (fun y => ((z.val : ℤ) - wy y) % q) xs ys) = xs.length * ys.length := by
  induction xs with
  | nil => simp [MatchPotential.count]
  | cons x xs ih =>
    simp only [MatchPotential.count]
    rw [Finset.sum_add_distrib, ih]
    have hf : (∑ z : Fin q, (ys.filter
        (fun y => decide (wx x % (q : ℤ) = ((z.val : ℤ) - wy y) % q))).length) = ys.length := by
      simp_rw [direct_match_iff hq]
      exact sum_filter_lengths (fun y => normalizedResidue hq (wx x + wy y)) ys
    rw [hf, List.length_cons, Nat.succ_mul]
    omega

def complement (hq : 0 < q) (t : ℤ) (z : Fin q) : Fin q :=
  normalizedResidue hq (t - z.val)

theorem complement_val (hq : 0 < q) (t : ℤ) (z : Fin q) :
    ((complement hq t z).val : ℤ) = (t - z.val) % q := by
  exact_mod_cast Int.toNat_of_nonneg (Int.emod_nonneg (t - z.val)
    (show (q : ℤ) ≠ 0 by exact_mod_cast hq.ne'))

theorem complement_involutive (hq : 0 < q) (t : ℤ) : Function.Involutive (complement hq t) := by
  intro z
  apply (normalizedResidue_eq_iff hq _ z).mpr
  rw [complement_val, Int.sub_emod_emod, sub_sub_cancel]
  exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast z.isLt)

def complementEquiv (hq : 0 < q) (t : ℤ) : Equiv.Perm (Fin q) :=
  (complement_involutive hq t).toPerm

theorem sum_complementary_potential (hq : 0 < q) (t : ℤ)
    (wx : α → ℤ) (wy : β → ℤ) (xs : List α) (ys : List β) :
    (∑ z : Fin q, MatchPotential.count (fun x => wx x % (q : ℤ))
      (fun y => (t - z.val - wy y) % q) xs ys) = xs.length * ys.length := by
  calc
    _ = ∑ z : Fin q, MatchPotential.count (fun x => wx x % (q : ℤ))
        (fun y => (((complement hq t z).val : ℤ) - wy y) % q) xs ys := by
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      funext y
      rw [complement_val, Int.emod_sub_emod]
    _ = ∑ z : Fin q, MatchPotential.count (fun x => wx x % (q : ℤ))
        (fun y => ((z.val : ℤ) - wy y) % q) xs ys :=
      Fintype.sum_equiv (complementEquiv hq t) _ _ (fun _ => rfl)
    _ = _ := sum_potential hq wx wy xs ys

end ResidueMatchAccounting
end LowSpaceSubsetSum

end OAI
