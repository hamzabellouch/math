import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafWork

namespace OAI

/-! # Bounded scans of an already stored finite set

The membership scan is tail recursive and visits the stored list once.
Its value, full-scan work, and constant workspace are invariant under list
permutation, so the executable descends through the multiset quotient
without extracting a representative by choice.
-/

namespace LowSpaceSubsetSum.FiniteSetCells

variable {n : ℕ}

def scan (i : Fin n) : List (Fin n) → Bool → ℕ → (Bool × ℕ) × ℕ
  | [], seen, work => ((seen, work+1), 8)
  | x :: xs, seen, work => scan i xs (seen || decide (i = x)) (work+1)

theorem scan_formula (i : Fin n) (xs : List (Fin n)) (seen : Bool) (work : ℕ) :
    scan i xs seen work = ((seen || decide (i ∈ xs), work+xs.length+1), 8) := by
  induction xs generalizing seen work with
  | nil => simp only [scan, List.not_mem_nil, decide_false, Bool.or_false,
      List.length_nil, Nat.add_zero]
  | cons x xs ih =>
    simp only [scan, ih, List.mem_cons, Bool.decide_or, List.length_cons]
    congr 2
    · simp only [Bool.or_assoc]
    · omega

def multisetMember (i : Fin n) (s : Multiset (Fin n)) : (Bool × ℕ) × ℕ :=
  Quot.liftOn s (fun xs => scan i xs false 0) (by
    intro xs ys h
    simp only [scan_formula, Bool.false_or, Nat.zero_add, h.length_eq, h.mem_iff])

theorem multisetMember_formula (i : Fin n) (s : Multiset (Fin n)) :
    multisetMember i s = ((decide (i ∈ s), s.card+1), 8) := by
  refine Quot.inductionOn s ?_
  intro xs
  change scan i xs false 0 = ((decide (i ∈ xs), xs.length+1), 8)
  simpa only [Bool.false_or, Nat.zero_add] using scan_formula i xs false 0

def member (V : Finset (Fin n)) (i : Fin n) : (Bool × ℕ) × ℕ := multisetMember i V.val

theorem member_formula (V : Finset (Fin n)) (i : Fin n) :
    member V i = ((decide (i ∈ V), V.card+1), 8) := by
  exact multisetMember_formula i V.val

def domain (V : Finset (Fin n)) : (List (Fin n) × ℕ) × ℕ :=
  let out := MeasuredFilterCells.run (member V) (List.finRange n)
  ((out.1.1, 2*(n+1)^2), out.2+4*n+2*V.card+16)

theorem domain_value (V : Finset (Fin n)) :
    (domain V).1 = RepresentationLeaf.domainSort V := by
  simp only [domain, MeasuredFilterCells.run_value, MeasuredFilter.runAcc_value,
    List.reverse_nil, List.nil_append, member_formula, RepresentationLeaf.domainSort]

theorem domain_cells (V : Finset (Fin n)) : (domain V).2 ≤ 8*n+28 := by
  have hm (i : Fin n) : (member V i).2 ≤ 8 := by rw [member_formula]
  have hf := MeasuredFilterCells.run_cells (member V) 8 hm (List.finRange n)
  have hv : V.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ V
  simp only [List.length_finRange] at hf
  change _+4*n+2*V.card+16 ≤ _
  omega

/-- The work of the full scans fits the domain reserve. -/
theorem domain_filter_work (V : Finset (Fin n)) :
    (MeasuredFilterCells.run (member V) (List.finRange n)).1.2 ≤ 2*(n+1)^2 := by
  have hm (i : Fin n) : (member V i).1.2 ≤ V.card+1 := by rw [member_formula]
  have hf := MeasuredFilter.runAcc_work (fun i => (member V i).1) (V.card+1) hm
    (List.finRange n) [] 0
  have hv : V.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ V
  rw [MeasuredFilterCells.run_value]
  simp only [List.length_finRange, List.length_nil, Nat.zero_add, Nat.add_zero] at hf
  have hmul := Nat.mul_le_mul_right n (show V.card+1+4 ≤ n+5 by omega)
  have hpoly : (n+5)*n+1 ≤ 2*(n+1)^2 := by
    cases n with
    | zero => norm_num
    | succ k => nlinarith [Nat.zero_le (k*k)]
  exact hf.trans ((Nat.add_le_add_right hmul 1).trans hpoly)

end LowSpaceSubsetSum.FiniteSetCells

end OAI
