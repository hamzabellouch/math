import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.RegisterProc

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing MachineCost TreeData

lemma exec_perm (P : Proc (Fin 3)) (e : Fin 3 ≃ Fin 3) (S T : Stack (Fin 3))
    (n : ℕ) (h : Exec P (S ∘ e) (T ∘ e) n) : Exec (reindex P e.toEmbedding) S T n := by
  have hf (S : Stack (Fin 3)) : frame e.toEmbedding (S (e 0)) (S (e 1)) (S (e 2)) S=S := by
    funext j
    obtain ⟨i,rfl⟩:=e.surjective j
    have hh:=StackEmbedding.extend_on e.toEmbedding ![S (e 0),S (e 1),S (e 2)] S i
    fin_cases i <;> exact hh
  have hs : S ∘ e=![S (e 0),S (e 1),S (e 2)] := by funext i; fin_cases i <;> rfl
  have ht : T ∘ e=![T (e 0),T (e 1),T (e 2)] := by funext i; fin_cases i <;> rfl
  rw [hs,ht] at h
  have hh:=exec_reindex P e.toEmbedding S _ _ _ _ _ _ n h
  rw [hf] at hh
  have hf' : frame e.toEmbedding (T (e 0)) (T (e 1)) (T (e 2)) S=T := by
    funext j
    obtain ⟨i,rfl⟩:=e.surjective j
    have he:=StackEmbedding.extend_on e.toEmbedding ![T (e 0),T (e 1),T (e 2)] S i
    fin_cases i <;> exact he
  rwa [hf'] at hh

def p02 : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
def p01 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def p12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
def p201 : Fin 3 ≃ Fin 3 := p02.trans p01

def p120 : Fin 3 ≃ Fin 3 := p201.symm
@[simp] lemma vector_p01 (A B C : List Bool) : ![A,B,C] ∘ p01=![B,A,C] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p02 (A B C : List Bool) : ![A,B,C] ∘ p02=![C,B,A] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p12 (A B C : List Bool) : ![A,B,C] ∘ p12=![A,C,B] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p201 (A B C : List Bool) : ![A,B,C] ∘ p201=![C,A,B] := by
  funext i; fin_cases i <;> rfl
@[simp] lemma vector_p120 (A B C : List Bool) : ![A,B,C] ∘ p120=![B,C,A] := by
  funext i; fin_cases i <;> rfl

def reverse02 : Proc (Fin 3) := reindex reverseRaw p12.toEmbedding
def reverse10 : Proc (Fin 3) := reindex reverseRaw p01.toEmbedding
def reverse20 : Proc (Fin 3) := reindex reverseRaw p201.toEmbedding
def reverse21 : Proc (Fin 3) := reindex reverseRaw p02.toEmbedding
lemma reverse02_exec (A B C : List Bool) :
    Exec reverse02 ![A,B,C] ![[],B,A.reverse++C] (A.length+1) := by
  apply exec_perm
  simpa only [vector_p12] using reverseRaw_exec A C B
lemma reverse10_exec (A B C : List Bool) :
    Exec reverse10 ![A,B,C] ![B.reverse++A,[],C] (B.length+1) := by
  apply exec_perm
  simpa only [vector_p01] using reverseRaw_exec B A C
lemma reverse20_exec (A B C : List Bool) :
    Exec reverse20 ![A,B,C] ![C.reverse++A,B,[]] (C.length+1) := by
  apply exec_perm
  simpa only [vector_p201] using reverseRaw_exec C A B
lemma reverse21_exec (A B C : List Bool) :
    Exec reverse21 ![A,B,C] ![A,C.reverse++B,[]] (C.length+1) := by
  apply exec_perm
  simpa only [vector_p02] using reverseRaw_exec C B A

def finishCons : Proc (Fin 3) := atom (.push 0 (fun _=>false) (.push 1 (fun _=>true) .halt))
lemma finishCons_exec (A : List Bool) : Exec finishCons ![[],A,[]] ![[false],true::A,[]] 1 := by
  apply exec_atom
  simp only [TM2.stepAux]
  congr 1
  funext i; fin_cases i <;> simp

def cons : Proc (Fin 3) := seq reverse02 (seq reverse21 finishCons)
lemma cons_exec (x y : Data) :
    Exec cons ![encode x,encode y,[]] ![encode .nil,encode (.cons x y),[]]
      (2*(encode x).length+3) := by
  have h₁:=reverse02_exec (encode x) (encode y) []
  have h₂:=reverse21_exec [] (encode y) (encode x).reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h₁ h₂
  have hh:=h₁.seq (h₂.seq (finishCons_exec (encode x++encode y)))
  exact hh.mono (by omega)

def clear1 : Proc (Fin 3) := reindex clearRaw p01.toEmbedding
lemma clear1_exec (A B C : List Bool) : Exec clear1 ![A,B,C] ![A,[],C] (B.length+1) := by
  apply exec_perm
  simpa only [vector_p01] using clearRaw_exec B A C

def copy : Proc (Fin 3) := seq clear1 (seq duplicateRaw (seq reverse10 reverse21))
lemma copy_exec (A B : List Bool) : Exec copy ![A,B,[]] ![A,A,[]]
    (B.length+3*A.length+4) := by
  have h₁:=clear1_exec A B []
  have h₂:=duplicateRaw_exec A [] []
  have h₃:=reverse10_exec [] A.reverse A.reverse
  have h₄:=reverse21_exec A [] A.reverse
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h₂ h₃ h₄
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  exact hh.mono (by omega)

def startSplit : Proc (Fin 3) := atom (.pop 1 (fun v _=>v) (.push 0 (fun _=>false) .halt))
lemma startSplit_exec (A : List Bool) : Exec startSplit ![[],true::A,[]] ![[false],A,[]] 1 := by
  apply exec_atom
  simp only [TM2.stepAux]
  congr 1
  funext i; fin_cases i <;> simp
def transfer12 : Proc (Fin 3) := reindex transferRaw p120.toEmbedding
lemma transfer12_exec (x : Data) (A B : List Bool) :
    Exec transfer12 ![[false],encode x++A,B] ![[],A,(encode x).reverse++B]
      ((encode x).length+1) := by
  apply exec_perm
  simpa only [vector_p120] using transferRaw_exec x A B

def split : Proc (Fin 3) := seq clearRaw (seq startSplit (seq transfer12 reverse20))
lemma split_exec (A : List Bool) (x y : Data) :
    Exec split ![A,encode (.cons x y),[]] ![encode x,encode y,[]]
      (A.length+2*(encode x).length+4) := by
  have h₁:=clearRaw_exec A (encode (.cons x y)) []
  have h₂:=startSplit_exec (encode x++encode y)
  have h₃:=transfer12_exec x (encode y) []
  have h₄:=reverse20_exec [] (encode y) (encode x).reverse
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h₃ h₄
  have hh:=h₁.seq (h₂.seq (h₃.seq h₄))
  exact hh.mono (by omega)
end MatchingFPRAS.RegisterProc

end OAI
