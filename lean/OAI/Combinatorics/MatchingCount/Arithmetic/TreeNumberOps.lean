import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.FiniteStore
import OAI.Combinatorics.MatchingCount.Tapes.TreeBits
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryNormalize

namespace OAI

namespace MatchingFPRAS.TreeBits
open Turing MachineCost RegisterProc BinaryNormalize TreeData

def decodeForward : Proc (Fin 3) := seq decodeRaw (reindex reverseRaw swap01)
lemma decodeForward_exec (A C : List Bool) :
    Exec decodeForward ![encode (bits A),[],C] ![A,[],C] (2*A.length+2) := by
  have h₁:=decodeRaw_exec A [] [] C
  simp only [List.append_nil] at h₁
  have h₂:=reindex_swap reverseRaw A.reverse [] C [] _ C _ (reverseRaw_exec A.reverse [] C)
  simp only [List.reverse_reverse,List.append_nil] at h₂
  apply (h₁.seq h₂).mono
  simp only [List.length_reverse]; omega

def encodeForward : Proc (Fin 3) := seq reverseRaw
  (seq (atom (.push 0 (fun _=>false) .halt)) (reindex encodeRaw swap01))
lemma encodeForward_exec (A C : List Bool) :
    Exec encodeForward ![A,[],C] ![encode (bits A),[],C] (2*A.length+3) := by
  have h₁:=reverseRaw_exec A [] C
  simp only [List.append_nil] at h₁
  have h₂ : Exec (atom (.push (0 : Fin 3) (fun _=>false) .halt))
      ![[],A.reverse,C] ![[false],A.reverse,C] 1 := by
    apply exec_atom
    simp only [TM2.stepAux]
    congr 1
    funext i; fin_cases i <;> simp
  have h₃:=reindex_swap encodeRaw A.reverse [false] C [] _ C _ (encodeRaw_exec A C)
  apply (h₁.seq (h₂.seq h₃)).mono
  omega
end MatchingFPRAS.TreeBits

namespace MatchingFPRAS.BinaryArithmeticProc
open RegisterProc Turing MachineCost

local instance addEntry : Inhabited (Bool⊕Unit) := ⟨.inl false⟩
def add : Proc (Fin 3) := FiniteStore.procedure ForwardAddition.program (default : StackAddition.Store)
lemma add_exec (A B : List Bool) :
    Exec add ![A,B,[]] ![StackAddition.addDigits false A B,[],[]] (2*(A.length+B.length)+3) := by
  obtain ⟨n,hn,he⟩:=ForwardAddition.run_add A B
  exact (FiniteStore.exec ForwardAddition.program default default _ _ n he).mono hn

local instance compareEntry : Inhabited Ordering := ⟨.eq⟩
def compare : Proc (Fin 3) := FiniteStore.procedure StackCompare.program (default : StackAddition.Store)
lemma compare_exec (A B : List Bool) :
    Exec compare ![A,B,[]] ![[],[],StackCompare.flags (Ord.compare (StackAddition.value A) (StackAddition.value B))]
      (A.length+B.length+1) := by
  obtain ⟨n,hn,he⟩:=StackCompare.run_comparison A B [] .eq default
  have h:=FiniteStore.exec StackCompare.program default default _ _ n he
  simp only [StackCompare.compares_values,List.append_nil] at h
  exact h.mono hn
end MatchingFPRAS.BinaryArithmeticProc

namespace MatchingFPRAS.TreeArithmetic
open RegisterProc TreeData TreeMachine Turing

variable {R : Type} [DecidableEq R]

def decode (i : R) : Proc (K R) := reindex TreeBits.decodeForward (singleEmbedding i)
def encode (i : R) : Proc (K R) := reindex TreeBits.encodeForward (singleEmbedding i)
def normalize (i : R) : Proc (K R) := reindex BinaryNormalize.program (singleEmbedding i)
def add (i j : R) (hij : i≠j) : Proc (K R) :=
  seq (decode i) (seq (decode j)
    (seq (reindex BinaryArithmeticProc.add (pairEmbedding i j hij))
      (seq (normalize i) (seq (encode i) (atom (.push (.inl j) (fun _=>false) .halt))))))

def rawPair (E : Env R) (i j : R) (A B : List Bool) : Stack (K R) :=
  Function.update (Function.update (encodeEnv E) (.inl i) A) (.inl j) B
lemma rawPair_scratch (E : Env R) (i j : R) (A B : List Bool) (k : Fin 2) :
    rawPair E i j A B (.inr k)=[] := by simp [rawPair,encodeEnv]
lemma rawPair_left (E : Env R) (i j : R) (hij : i≠j) (A B : List Bool) :
    rawPair E i j A B (.inl i)=A := by simp [rawPair,hij]
lemma rawPair_right (E : Env R) (i j : R) (A B : List Bool) :
    rawPair E i j A B (.inl j)=B := by simp [rawPair]
lemma rawPair_encode (E : Env R) (i j : R) (x y : Data) :
    rawPair E i j (TreeData.encode x) (TreeData.encode y)=encodeEnv (putPair E i j x y) := by
  funext k
  cases k with
  | inr k => simp [rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [rawPair,encodeEnv,putPair]
lemma rawPair_same (E : Env R) (i j : R) :
    rawPair E i j (TreeData.encode (E i)) (TreeData.encode (E j))=encodeEnv E := by
  funext k
  cases k with
  | inr k => simp [rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [rawPair,encodeEnv]
lemma put3_raw_left (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) :
    put3 (rawPair E i j A B) (.inl i) (.inr 0) (.inr 1) F [] []=rawPair E i j F B := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
lemma put3_raw_right (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) :
    put3 (rawPair E i j A B) (.inl j) (.inr 0) (.inr 1) F [] []=rawPair E i j A F := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
  | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
lemma on_left (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) (n : ℕ)
    (h : Exec P ![A,[],[]] ![F,[],[]] n) :
    Exec (reindex P (singleEmbedding i)) (rawPair E i j A B) (rawPair E i j F B) n := by
  have hh:=exec_on P (.inl i : K R) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (rawPair E i j A B) F [] [] n
  rw [rawPair_left E i j hij,rawPair_scratch,rawPair_scratch] at hh
  simpa only [singleEmbedding,put3_raw_left E i j hij] using hh h
lemma on_right (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F : List Bool) (n : ℕ)
    (h : Exec P ![B,[],[]] ![F,[],[]] n) :
    Exec (reindex P (singleEmbedding j)) (rawPair E i j A B) (rawPair E i j A F) n := by
  have hh:=exec_on P (.inl j : K R) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (rawPair E i j A B) F [] [] n
  rw [rawPair_right,rawPair_scratch,rawPair_scratch] at hh
  simpa only [singleEmbedding,put3_raw_right E i j hij] using hh h
lemma on_pair (P : Proc (Fin 3)) (E : Env R) (i j : R) (hij : i≠j) (A B F G : List Bool) (n : ℕ)
    (h : Exec P ![A,B,[]] ![F,G,[]] n) :
    Exec (reindex P (pairEmbedding i j hij)) (rawPair E i j A B) (rawPair E i j F G) n := by
  have hh:=exec_on P (.inl i : K R) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (rawPair E i j A B) F G [] n
  rw [rawPair_left E i j hij,rawPair_right,rawPair_scratch] at hh
  have he : put3 (rawPair E i j A B) (.inl i) (.inl j) (.inr 0) F G []=rawPair E i j F G := by
    funext k
    cases k with
    | inr k => fin_cases k <;> simp [put3,rawPair,encodeEnv]
    | inl k => by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,rawPair]
  exact he ▸ hh h

theorem add_exec (E : Env R) (i j : R) (hij : i≠j) (m n : ℕ)
    (hm : E i=nat m) (hn : E j=nat n) :
    Exec (add i j hij) (encodeEnv E) (encodeEnv (putPair E i j (nat (m+n)) .nil))
      (9*(m.bits.length+n.bits.length)+20) := by
  let A:=m.bits
  let B:=n.bits
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
  have hS : BinaryNormalize.normalize S=(m+n).bits := by
    rw [BinaryNormalize.normalize_bits,StackAddition.addition_numerals]
  rw [hS] at hh
  have hstart : rawPair E i j (TreeData.encode (bits A)) (TreeData.encode (bits B))=encodeEnv E := by
    change rawPair E i j (TreeData.encode (nat m)) (TreeData.encode (nat n))=encodeEnv E
    rw [←hm,←hn]
    exact rawPair_same E i j
  have hend : rawPair E i j (TreeData.encode (bits (m+n).bits)) [false]=
      encodeEnv (putPair E i j (nat (m+n)) .nil) := rawPair_encode E i j (nat (m+n)) .nil
  rw [hstart,hend] at hh
  apply hh.mono
  have hl:=StackAddition.addDigits_length A B false
  have hl' := BinaryNormalize.normalize_length S
  rw [hS] at hl'
  dsimp only [A,B,S] at hl hl' ⊢
  omega
end MatchingFPRAS.TreeArithmetic

end OAI
