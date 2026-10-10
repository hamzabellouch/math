import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeNumberOps

namespace OAI

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

theorem add_bits_exec (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool)
    (hm : E i=bits A) (hn : E j=bits B) :
    Exec (add i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (StackAddition.value A+StackAddition.value B)) .nil))
      (9*(A.length+B.length)+20) := by
  let S:=StackAddition.addDigits false A B
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.add E i j hij A B S [] _ (BinaryArithmeticProc.add_exec A B)
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
  have hS : BinaryNormalize.normalize S=(StackAddition.value A+StackAddition.value B).bits := by
    rw [BinaryNormalize.normalize_bits,StackAddition.addDigits_value,Bool.toNat_false,Nat.add_zero]
  rw [hS] at hh
  have hstart : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    rw [←hm,←hn]
    exact rawPair_same E i j
  have hend : rawPair E i j (TreeData.encode (bits (StackAddition.value A+StackAddition.value B).bits)) [false]=
      encodeEnv (putPair E i j (nat (StackAddition.value A+StackAddition.value B)) .nil) := rawPair_encode E i j (nat (StackAddition.value A+StackAddition.value B)) .nil
  rw [hstart,hend] at hh
  apply hh.mono
  have hl:=StackAddition.addDigits_length A B false
  have hl' := BinaryNormalize.normalize_length S
  rw [hS] at hl'
  dsimp only [S] at hl hl' ⊢
  omega
end MatchingFPRAS.TreeArithmetic

end OAI
