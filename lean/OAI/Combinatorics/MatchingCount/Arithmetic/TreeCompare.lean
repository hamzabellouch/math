import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeNumberOps

namespace OAI

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc TreeData Turing

def pickLt : Proc (Fin 3) := atom
  (.pop 2 (fun _ x=>x) (.pop 2 (fun x _=>x)
    (.branch (fun x=>x.getD false)
      (.push 0 (fun _=>false) (.push 0 (fun _=>false) (.push 0 (fun _=>true)
        (.load (fun _=>none) .halt))))
      (.push 0 (fun _=>false) (.load (fun _=>none) .halt)))))
lemma pickLt_exec (c : Ordering) :
    Exec pickLt ![[],[],StackCompare.flags c] ![encode (bit (decide (c=.lt))),[],[]] 1 := by
  apply exec_atom
  cases c <;> simp [TM2.stepAux,StackCompare.flags,encode,bit]
  all_goals funext k; fin_cases k <;> simp

def less : Proc (Fin 3) := seq compare pickLt
lemma less_exec (A B : List Bool) :
    Exec less ![A,B,[]] ![encode (bit (decide (StackAddition.value A<StackAddition.value B))),[],[]]
      (A.length+B.length+2) := by
  have hh:=(compare_exec A B).seq (pickLt_exec (Ord.compare (StackAddition.value A) (StackAddition.value B)))
  simp only [compare_lt_iff_lt] at hh
  exact hh.mono (by omega)
end MatchingFPRAS.BinaryArithmeticProc

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def less (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j) (seq (reindex BinaryArithmeticProc.less (pairEmbedding i j hij))
    (atom (.push (.inl j) (fun _=>false) .halt))))

theorem less_bits_exec (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool)
    (hi : E i=bits A) (hj : E j=bits B) :
    Exec (less i j hij) (encodeEnv E)
      (encodeEnv (putPair E i j (bit (decide (StackAddition.value A<StackAddition.value B))) .nil))
      (3*(A.length+B.length)+7) := by
  have h₁:=on_left TreeBits.decodeForward E i j hij (TreeData.encode (bits A)) (TreeData.encode (bits B)) A _
    (TreeBits.decodeForward_exec A [])
  have h₂:=on_right TreeBits.decodeForward E i j hij A (TreeData.encode (bits B)) B _
    (TreeBits.decodeForward_exec B [])
  have h₃:=on_pair BinaryArithmeticProc.less E i j hij A B _ [] _ (BinaryArithmeticProc.less_exec A B)
  have h₄ : Exec (atom (.push (.inl j) (fun _=>false) .halt))
      (rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [])
      (rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [false]) 1 := by
    apply exec_atom
    simp only [TM2.stepAux,rawPair_right]
    congr 1
    simp [rawPair]
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  have hs : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    rw [←hi,←hj]; exact rawPair_same E i j
  have he : rawPair E i j (TreeData.encode (bit (decide (StackAddition.value A<StackAddition.value B)))) [false]=
      encodeEnv (putPair E i j (bit (decide (StackAddition.value A<StackAddition.value B))) .nil) :=
    rawPair_encode E i j _ .nil
  rw [hs,he] at hh
  exact hh.mono (by omega)

lemma less_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hi : E i=nat m) (hj : E j=nat n) :
    Exec (less i j hij) (encodeEnv E) (encodeEnv (putPair E i j (bit (decide (m<n))) .nil))
      (3*(m.bits.length+n.bits.length)+7) := by
  simpa only [StackAddition.value_bits] using less_bits_exec E i j hij m.bits n.bits hi hj
end MatchingFPRAS.TreeArithmetic

end OAI
