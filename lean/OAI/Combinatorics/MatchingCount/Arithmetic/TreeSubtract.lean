import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeNumberOps
import OAI.Combinatorics.MatchingCount.Arithmetic.SubtractProc

namespace OAI

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def sub (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j)
    (seq (reindex BinaryArithmeticProc.sub (pairEmbedding i j hij))
      (seq (normalize i) (seq (encode i) (atom (.push (.inl j) (fun _=>false) .halt))))))

theorem sub_bits_exec (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool)
    (hm : E i=bits A) (hn : E j=bits B) (hle : StackAddition.value B≤StackAddition.value A) :
    Exec (sub i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (StackAddition.value A-StackAddition.value B)) .nil))
      (9*(A.length+B.length)+20) := by
  let S:=(StackSubtract.subDigits false A B).2
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.sub E i j hij A B S [] _ (BinaryArithmeticProc.sub_exec A B)
  have h₄:=on_left BinaryNormalize.program E i j hij S [] (BinaryNormalize.normalize S) _
    (BinaryNormalize.exec S [])
  have h₅:=on_left TreeBits.encodeForward E i j hij (BinaryNormalize.normalize S) []
    (TreeData.encode (bits (BinaryNormalize.normalize S))) _ (TreeBits.encodeForward_exec _ [])
  have h₆ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [])
      (rawPair E i j (TreeData.encode (bits (BinaryNormalize.normalize S))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  have hS : BinaryNormalize.normalize S=(StackAddition.value A-StackAddition.value B).bits := by
    rw [BinaryNormalize.normalize_bits]
    congr 1
    simpa only [Bool.toNat_false,Nat.add_zero,Nat.sub_zero] using
      (StackSubtract.subDigits_correct A B false (by simpa using hle)).2
  rw [hS] at hh
  have hstart : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    rw [←hm,←hn]
    exact rawPair_same E i j
  have hend : rawPair E i j (TreeData.encode (bits (StackAddition.value A-StackAddition.value B).bits)) [false]=
      encodeEnv (putPair E i j (nat (StackAddition.value A-StackAddition.value B)) .nil) := rawPair_encode E i j (nat (StackAddition.value A-StackAddition.value B)) .nil
  rw [hstart,hend] at hh
  apply hh.mono
  have hl:=StackSubtract.subDigits_length A B false
  have hl' := BinaryNormalize.normalize_length S
  rw [hS] at hl'
  dsimp only [S] at hl hl' ⊢
  omega

lemma sub_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hi : E i=nat m) (hj : E j=nat n) (hle : n ≤ m) :
    Exec (sub i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (m-n)) .nil))
      (9*(m.bits.length+n.bits.length)+20) := by
  simpa only [StackAddition.value_bits] using sub_bits_exec E i j hij m.bits n.bits hi hj
    (by simpa only [StackAddition.value_bits] using hle)
end MatchingFPRAS.TreeArithmetic

end OAI
