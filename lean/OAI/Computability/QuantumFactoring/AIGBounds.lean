import Mathlib

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGBounds
open Std.Sat
open Std.Tactic.BVDecide.BVExpr.bitblast

variable {α : Type} [Hashable α] [DecidableEq α]

lemma cached_go_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (AIG.mkGateCached.go aig input).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkGateCached.go]
  split
  · simp
  · split <;> try simp
    split
    · split <;> simp
    · simp

lemma cached_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkGateCached input).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkGateCached]
  split <;> apply cached_go_size

lemma atom_size (aig : AIG α) (v : α) :
    (aig.mkAtomCached v).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkAtomCached]
  split <;> simp

lemma and_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkAndCached input).aig.decls.size ≤ aig.decls.size + 1 := cached_size _ _

lemma or_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkOrCached input).aig.decls.size ≤ aig.decls.size + 1 := cached_size _ _

lemma xor_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkXorCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkXorCached
  dsimp only
  exact (cached_size _ _).trans (by
    have := cached_size aig input
    have := cached_size (aig.mkGateCached input).aig
      ((input.cast (AIG.LawfulOperator.le_size ..)).invert true true)
    omega)

lemma fullAdderOut_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdderOut aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderOut
  dsimp only
  exact (xor_size _ _).trans (by
    have := xor_size aig ⟨input.lhs,input.rhs⟩
    omega)

lemma fullAdderCarry_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdderCarry aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderCarry
  dsimp only
  apply (or_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  exact xor_size _ _

lemma fullAdder_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdder aig input).aig.decls.size ≤ aig.decls.size + 12 := by
  unfold mkFullAdder
  dsimp only
  apply (fullAdderCarry_size _ _).trans
  have := fullAdderOut_size aig input
  omega

lemma add_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (hcurr : curr ≤ w) (cin : AIG.Ref aig) (s : AIG.RefVec aig curr) :
    (blastAdd.go aig lhs rhs curr hcurr cin s).aig.decls.size ≤
      aig.decls.size + 12*(w-curr) := by
  rw [blastAdd.go]
  split
  next h =>
    dsimp only
    apply (add_go_size _ _ _ _ _ _ _).trans
    have hh := fullAdder_size aig ⟨lhs.get curr h, rhs.get curr h, cin⟩
    omega
  next h => simp
termination_by w-curr

/-- A verified native ripple circuit has linear declaration count. The cache
can only decrease this upper bound. -/
theorem add_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastAdd aig input).aig.decls.size ≤ aig.decls.size + 12*w := by
  unfold blastAdd
  split <;> unfold blastAdd.blast <;> apply add_go_size

lemma if_size (aig : AIG α) (input : AIG.TernaryInput aig) :
    (aig.mkIfCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkIfCached
  dsimp only
  apply (or_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  exact and_size _ _

lemma ite_go_size {w : ℕ} (aig : AIG α) (curr : ℕ) (hcurr : curr ≤ w)
    (discr : AIG.Ref aig) (lhs rhs : AIG.RefVec aig w) (s : AIG.RefVec aig curr) :
    (AIG.RefVec.ite.go aig curr hcurr discr lhs rhs s).aig.decls.size ≤
      aig.decls.size + 3*(w-curr) := by
  rw [AIG.RefVec.ite.go]
  split
  next h =>
    dsimp only
    apply (ite_go_size _ _ _ _ _ _ _).trans
    have hh := if_size aig ⟨discr, lhs.get curr h, rhs.get curr h⟩
    omega
  next h => simp
termination_by w-curr

lemma ite_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec.IfInput aig w) :
    (AIG.RefVec.ite aig input).aig.decls.size ≤ aig.decls.size + 3*w :=
  ite_go_size _ 0 _ _ _ _ _

lemma shift_go_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w)
    (distance curr : ℕ) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    (blastShiftLeftConst.go aig input distance curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastShiftLeftConst.go]
  split
  · split <;> apply shift_go_size
  · simp
termination_by w-curr

lemma shift_size {w : ℕ} (aig : AIG α) (input : AIG.ShiftTarget aig w) :
    (blastShiftLeftConst aig input).aig.decls.size = aig.decls.size := shift_go_size ..

lemma mul_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (acc : AIG.RefVec aig w) :
    (blastMul.go aig lhs rhs curr acc).aig.decls.size ≤ aig.decls.size + 15*w*(w-curr) := by
  rw [blastMul.go]
  split
  next h =>
    split
    · apply (mul_go_size _ _ _ _ _).trans
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    · dsimp only
      apply (mul_go_size _ _ _ _ _).trans
      have hshift := shift_size aig ⟨lhs,curr⟩
      refine (Nat.add_le_add_right (ite_size _ _) _).trans ?_
      have hadd : (blastAdd (blastShiftLeftConst aig ⟨lhs,curr⟩).aig
            ⟨acc.cast (AIG.LawfulVecOperator.le_size ..),
              (blastShiftLeftConst aig ⟨lhs,curr⟩).vec⟩).aig.decls.size ≤ aig.decls.size + 12*w := by
          rw [← hshift]
          apply add_size
      have he : w-curr = (w-(curr+1))+1 := by omega
      rw [he, Nat.mul_add, Nat.mul_one]
      omega
  next h => simp
termination_by w-curr

lemma mul_blast_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastMul.blast aig input).aig.decls.size ≤ aig.decls.size + 15*w*w := by
  unfold blastMul.blast
  split
  · simp_all
  next h =>
    dsimp only
    apply (mul_go_size _ _ _ _ _).trans
    have hh := ite_size aig ⟨input.rhs.get 0 (by omega), input.lhs, blastConst aig 0⟩
    have he : w-1+1=w := by omega
    nlinarith

/-- The native shift-and-add multiplier has quadratic declaration count. -/
theorem mul_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastMul aig input).aig.decls.size ≤ aig.decls.size + 15*w*w := by
  unfold blastMul
  split <;> apply mul_blast_size

end ExactQuantumFactoring.AIGBounds


end

end OAI
