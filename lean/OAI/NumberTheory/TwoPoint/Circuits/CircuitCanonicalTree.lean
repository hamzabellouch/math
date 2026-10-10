import OAI.NumberTheory.TwoPoint.Circuits.CircuitPartialAssignment
import OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionTree

namespace OAI

/-! The canonical tree queries the unset variables of the first compatible
term, then continues through the remaining terms. This concrete tree is the
one encoded in the switching argument. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace BooleanDecisionTree

def queryVariables {n : ℕ} : List (Fin n) →
    (PartialAssignment n → BooleanDecisionTree n) → PartialAssignment n → BooleanDecisionTree n
  | [], k, ρ => k ρ
  | i :: is, k, ρ => .query i
      (queryVariables is k (Function.update ρ i (some false)))
      (queryVariables is k (Function.update ρ i (some true)))

lemma queryVariables_eval {n : ℕ} (is : List (Fin n))
    (k : PartialAssignment n → BooleanDecisionTree n) (ρ : PartialAssignment n)
    (x : BooleanCube n) :
    (queryVariables is k ρ).eval x = (k (ρ.assign is.toFinset x)).eval x := by
  induction is generalizing ρ with
  | nil => simp [queryVariables]
  | cons i is ih =>
    simp only [queryVariables, eval]
    cases hx : x i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · rw [ih]
      have ha := PartialAssignment.assign_insert ρ is.toFinset x i
      rw [hx] at ha
      simp only [List.toFinset_cons, ha]
    · rw [ih]
      have ha := PartialAssignment.assign_insert ρ is.toFinset x i
      rw [hx] at ha
      simp only [List.toFinset_cons, ha]

lemma queryVariables_depth_le {n d : ℕ} (is : List (Fin n))
    (k : PartialAssignment n → BooleanDecisionTree n)
    (hk : ∀ ρ, (k ρ).depth ≤ d) (ρ : PartialAssignment n) :
    (queryVariables is k ρ).depth ≤ is.length + d := by
  induction is generalizing ρ with
  | nil => simpa only [queryVariables, List.length_nil, Nat.zero_add] using hk ρ
  | cons i is ih =>
    change max _ _ + 1 ≤ _
    have hl := ih (Function.update ρ i (some false))
    have hh := ih (Function.update ρ i (some true))
    have hm := max_le hl hh
    simpa only [List.length_cons, Nat.add_right_comm] using Nat.add_le_add_right hm 1

end BooleanDecisionTree

def dnfEval {n : ℕ} (F : List (CubeTerm n)) (x : BooleanCube n) : Bool :=
  F.any (fun C => C.eval x)

noncomputable def canonicalDNFTree {n : ℕ} :
    List (CubeTerm n) → PartialAssignment n → BooleanDecisionTree n
  | [], _ => .leaf false
  | C :: F, ρ =>
      if C.Compatible ρ then
        BooleanDecisionTree.queryVariables ((C.live ρ).sort (· ≤ ·))
          (fun τ => if C.Satisfied τ then .leaf true else canonicalDNFTree F τ) ρ
      else canonicalDNFTree F ρ

theorem canonicalDNFTree_eval {n : ℕ} (F : List (CubeTerm n))
    (ρ : PartialAssignment n) (x : BooleanCube n) :
    (canonicalDNFTree F ρ).eval x = dnfEval F (ρ.apply x) := by
  induction F generalizing ρ with
  | nil => simp [canonicalDNFTree, dnfEval, BooleanDecisionTree.eval]
  | cons C F ih =>
    by_cases hC : C.Compatible ρ
    · rw [canonicalDNFTree, ite_eq_left hC, BooleanDecisionTree.queryVariables_eval]
      simp only [Finset.sort_toFinset]
      have happly := ρ.apply_assign_free (C.live ρ) (C.live_subset_free ρ) x
      have hs := C.satisfied_assign_live_iff ρ hC x
      by_cases hsat : C.Satisfied (ρ.assign (C.live ρ) x)
      · have he := hs.mp hsat
        simp [hsat, BooleanDecisionTree.eval, dnfEval, he]
      · have he : C.eval (ρ.apply x) = false := Bool.eq_false_iff.mpr (mt hs.mpr hsat)
        simp only [hsat, ite_false, ih, happly, dnfEval, List.any_cons, he,
          Bool.false_or]
    · have he := C.eval_apply_of_incompatible ρ hC x
      simp only [canonicalDNFTree, hC, ite_false, ih, dnfEval, List.any_cons, he,
        Bool.false_or]

end TwoPointCorrelations

end OAI
