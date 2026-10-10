import Mathlib
import OAI.Computability.QuantumFactoring.AIGBounds

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGBounds
open Std.Sat Std.Tactic.BVDecide
open BVExpr.bitblast
variable {α : Type} [Hashable α] [DecidableEq α]

lemma not_go_size {w : ℕ} (aig : AIG α) (i : ℕ) (hi : i ≤ w)
    (s : AIG.RefVec aig i) (input : AIG.RefVec aig w) :
    (AIG.RefVec.map.go aig i hi s input AIG.mkNotCached).aig.decls.size = aig.decls.size := by
  rw [AIG.RefVec.map.go]
  split
  · dsimp only
    rw [not_go_size]
    rfl
  · rfl
termination_by w-i

lemma not_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (blastNot aig input).aig.decls.size = aig.decls.size :=
  not_go_size ..

lemma neg_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (blastNeg aig input).aig.decls.size ≤ aig.decls.size+12*w := by
  unfold blastNeg
  have h := add_size (blastNot aig input).aig
    ⟨(blastNot aig input).vec, blastConst (blastNot aig input).aig (1#w)⟩
  simpa only [not_size] using h

lemma sub_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastSub aig input).aig.decls.size ≤ aig.decls.size+24*w := by
  unfold blastSub
  dsimp only
  apply (add_size _ _).trans
  have h := neg_size aig input.rhs
  omega

lemma overflow_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (cin : AIG.Ref aig) :
    (mkOverflowBit.go aig lhs rhs curr cin).aig.decls.size ≤
      aig.decls.size+6*(w-curr) := by
  rw [mkOverflowBit.go]
  split
  next h =>
    dsimp only
    apply (overflow_go_size _ _ _ _ _).trans
    have hh := fullAdderCarry_size aig ⟨lhs.get curr h, rhs.get curr h, cin⟩
    omega
  · simp
termination_by w-curr

lemma overflow_size (aig : AIG α) (input : OverflowInput aig) :
    (mkOverflowBit aig input).aig.decls.size ≤ aig.decls.size+6*input.w :=
  overflow_go_size ..

lemma ult_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkUlt aig input).aig.decls.size ≤ aig.decls.size+6*w := by
  unfold BVPred.mkUlt
  dsimp only
  change (mkOverflowBit _ _).aig.decls.size ≤ _
  apply (overflow_size _ _).trans
  simp only [not_size, le_refl]

lemma extend_go_size (aig : AIG α) (w : ℕ) (input : AIG.RefVec aig w)
    (newWidth curr : ℕ) (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
    (blastZeroExtend.go aig w input newWidth curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastZeroExtend.go]
  split
  · dsimp only
    split <;> apply extend_go_size
  · rfl
termination_by newWidth-curr

lemma extend_size {w : ℕ} (aig : AIG α) (input : AIG.ExtendTarget aig w) :
    (blastZeroExtend aig input).aig.decls.size = aig.decls.size := extend_go_size ..

lemma shiftConcat_size {w : ℕ} (aig : AIG α) (input : blastUdiv.ShiftConcatInput aig w) :
    (blastUdiv.blastShiftConcat aig input).aig.decls.size = aig.decls.size := extend_size ..

lemma div_step_size {w : ℕ} (aig : AIG α) (n d : AIG.RefVec aig w)
    (wn wr : ℕ) (q r : AIG.RefVec aig w) :
    (blastUdiv.blastDivSubtractShift aig n d wn wr q r).aig.decls.size ≤
      aig.decls.size+36*w := by
  unfold blastUdiv.blastDivSubtractShift
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (ite_size _ _) (3*w)).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right (ult_size _ _) (3*w)) (3*w)).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (sub_size _ _) (6*w)) (3*w)) (3*w)).trans
  simp only [shiftConcat_size]
  omega

lemma div_go_size {w : ℕ} (aig : AIG α) (curr : ℕ) (n d : AIG.RefVec aig w)
    (wn wr : ℕ) (q r : AIG.RefVec aig w) :
    (blastUdiv.go aig curr n d wn wr q r).aig.decls.size ≤ aig.decls.size+36*w*curr := by
  induction curr generalizing aig wn wr with
  | zero => simp [blastUdiv.go]
  | succ curr ih =>
    rw [blastUdiv.go]
    dsimp only
    apply (ih _ _ _ _ _ _ _).trans
    have h := div_step_size aig n d wn wr q r
    nlinarith

lemma beq_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkBEqCached input).aig.decls.size ≤ aig.decls.size+3 := by
  unfold AIG.mkBEqCached
  dsimp only
  apply (cached_size _ _).trans
  apply (Nat.add_le_add_right (cached_size _ _) 1).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right (cached_size _ _) 1) 1).trans
  omega

lemma zip_go_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator α f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (idx : ℕ) (s : AIG.RefVec aig idx) (hi : idx ≤ w)
    (lhs rhs : AIG.RefVec aig w) :
    (AIG.RefVec.zip.go aig idx s hi lhs rhs f).aig.decls.size ≤ aig.decls.size+c*(w-idx) := by
  rw [AIG.RefVec.zip.go]
  split
  next h =>
    dsimp only
    apply (zip_go_size f c hf _ _ _ _ _ _).trans
    have hh := hf aig ⟨lhs.get idx h, rhs.get idx h⟩
    have he : w-idx = w-(idx+1)+1 := by omega
    rw [he]
    nlinarith
  · simp
termination_by w-idx

lemma zip_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator α f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (AIG.RefVec.zip aig input f).aig.decls.size ≤ aig.decls.size+c*w := zip_go_size f c hf aig 0 _ (by omega) input.lhs input.rhs

lemma fold_go_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (acc : AIG.Ref aig) (idx : ℕ) (input : AIG.RefVec aig w) :
    (AIG.RefVec.fold.go aig acc idx w input f).aig.decls.size ≤ aig.decls.size+c*(w-idx) := by
  rw [AIG.RefVec.fold.go]
  split
  next h =>
    dsimp only
    apply (fold_go_size f c hf _ _ _ _).trans
    have hh := hf aig ⟨acc, input.get idx h⟩
    have he : w-idx = w-(idx+1)+1 := by omega
    rw [he]
    nlinarith
  · simp
termination_by w-idx

lemma fold_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (AIG.RefVec.fold aig input f).aig.decls.size ≤ aig.decls.size+c*w := fold_go_size f c hf aig (aig.mkConstCached true) 0 input

lemma eq_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkEq aig input).aig.decls.size ≤ aig.decls.size+4*w := by
  unfold BVPred.mkEq
  dsimp only
  apply (fold_size _ 1 and_size _ _).trans
  have hh := zip_size _ 3 beq_size aig input
  omega

lemma div_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastUdiv aig input).aig.decls.size ≤ aig.decls.size+36*w*w+7*w := by
  unfold blastUdiv
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (div_go_size _ _ _ _ _ _ _ _) (3*w)).trans
  have hh := eq_size aig ⟨input.rhs, blastConst aig 0#w⟩
  omega

lemma mod_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastUmod aig input).aig.decls.size ≤ aig.decls.size+36*w*w+7*w := by
  unfold blastUmod
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (div_go_size _ _ _ _ _ _ _ _) (3*w)).trans
  have hh := eq_size aig ⟨input.rhs, blastConst aig 0#w⟩
  omega

end ExactQuantumFactoring.AIGBounds


end

end OAI
