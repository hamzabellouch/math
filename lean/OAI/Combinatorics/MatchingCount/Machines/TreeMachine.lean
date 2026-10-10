import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.RegisterTree

namespace OAI

namespace MatchingFPRAS.RegisterProc
open Turing TreeData

def makeNil : Proc (Fin 3) := seq clearRaw (atom (.push 0 (fun _=>false) .halt))
lemma makeNil_exec (A B C : List Bool) : Exec makeNil ![A,B,C] ![[false],B,C] (A.length+2) := by
  have h₁:=clearRaw_exec A B C
  have h₂ : Exec (atom (.push 0 (fun _=>false) .halt)) ![[],B,C] ![[false],B,C] 1 := by
    apply exec_atom
    simp only [TM2.stepAux]
    congr 1
    funext i; fin_cases i <;> simp
  exact (h₁.seq h₂).mono (by omega)

variable {K : Type} [DecidableEq K]
lemma exec_on (P : Proc (Fin 3)) (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (S : Stack K) (A B C : List Bool) (n : ℕ)
    (h : Exec P ![S a,S b,S c] ![A,B,C] n) :
    Exec (reindex P (triple a b c hab hac hbc)) S (put3 S a b c A B C) n := by
  have hh:=exec_reindex P (triple a b c hab hac hbc) S _ _ _ _ _ _ n h
  simpa only [frame_triple,put3_same S a b c hab hac hbc] using hh
end MatchingFPRAS.RegisterProc

namespace MatchingFPRAS.TreeMachine
open TreeData RegisterProc Turing MachineCost

variable {R Λ : Type} [DecidableEq R]
abbrev K (R : Type) := R⊕Fin 2
abbrev Env (R : Type) := R→Data

def encodeEnv (E : Env R) : Stack (K R)
  | .inl r => encode (E r)
  | .inr _ => []
def pairEmbedding (i j : R) (hij : i≠j) : Fin 3 ↪ K R :=
  triple (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
def singleEmbedding (i : R) : Fin 3 ↪ K R :=
  triple (.inl i) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)

def putPair (E : Env R) (i j : R) (x y : Data) : Env R :=
  Function.update (Function.update E i x) j y
lemma encode_putPair (E : Env R) (i j : R) (hij : i≠j) (x y : Data) :
    put3 (encodeEnv E) (.inl i) (.inl j) (.inr 0) (encode x) (encode y) []=
      encodeEnv (putPair E i j x y) := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,encodeEnv]
  | inl k =>
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [put3,encodeEnv,putPair]
lemma encode_putSingle (E : Env R) (i : R) (x : Data) :
    put3 (encodeEnv E) (.inl i) (.inr 0) (.inr 1) (encode x) [] []=
      encodeEnv (Function.update E i x) := by
  funext k
  cases k with
  | inr k => fin_cases k <;> simp [put3,encodeEnv]
  | inl k => by_cases hi : k=i <;> simp_all [put3,encodeEnv]

inductive Instr (R Λ : Type) where
  | halt
  | go (next : Λ)
  | branch (i : R) (nil cons : Λ)
  | nil (i : R) (next : Λ)
  | copy (i j : R) (distinct : i≠j) (next : Λ)
  | cons (i j : R) (distinct : i≠j) (next : Λ)
  | split (i j : R) (distinct : i≠j) (next : Λ)

def procedure : Instr R Λ → Proc (K R)
  | .nil i _ => reindex makeNil (singleEmbedding i)
  | .copy i j h _ => reindex RegisterProc.copy (pairEmbedding i j h)
  | .cons i j h _ => reindex RegisterProc.cons (pairEmbedding i j h)
  | .split i j h _ => reindex RegisterProc.split (pairEmbedding i j h)
  | _ => atom .halt

def successor : Instr R Λ → Option Λ
  | .nil _ l | .copy _ _ _ l | .cons _ _ _ l | .split _ _ _ l => some l
  | _ => none

lemma nil_exec (E : Env R) (i : R) (l : Λ) :
    Exec (procedure (.nil i l)) (encodeEnv E) (encodeEnv (Function.update E i .nil))
      ((encode (E i)).length+2) := by
  have hh:=exec_on (K:=K R) makeNil (.inl i) (.inr 0) (.inr 1) (by simp) (by simp) (by simp)
    (encodeEnv E) [false] [] [] _ (makeNil_exec (encode (E i)) [] [])
  have he:=encode_putSingle E i .nil
  simp only [encode] at he
  rwa [he] at hh
lemma copy_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) :
    Exec (procedure (.copy i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j (E i) (E i)))
      ((encode (E j)).length+3*(encode (E i)).length+4) := by
  have hh:=exec_on (K:=K R) RegisterProc.copy (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode (E i)) (encode (E i)) [] _ (RegisterProc.copy_exec (encode (E i)) (encode (E j)))
  rwa [encode_putPair E i j hij] at hh
lemma cons_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) :
    Exec (procedure (.cons i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j .nil (.cons (E i) (E j))))
      (2*(encode (E i)).length+3) := by
  have hh:=exec_on (K:=K R) RegisterProc.cons (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode .nil) (encode (.cons (E i) (E j))) [] _ (RegisterProc.cons_exec (E i) (E j))
  rwa [encode_putPair E i j hij] at hh
lemma split_exec (E : Env R) (i j : R) (hij : i≠j) (l : Λ) (x y : Data) (he : E j=.cons x y) :
    Exec (procedure (.split i j hij l)) (encodeEnv E) (encodeEnv (putPair E i j x y))
      ((encode (E i)).length+2*(encode x).length+4) := by
  have h:=RegisterProc.split_exec (encode (E i)) x y
  rw [←he] at h
  have hh:=exec_on (K:=K R) RegisterProc.split (.inl i) (.inl j) (.inr 0) (by simpa) (by simp) (by simp)
    (encodeEnv E) (encode x) (encode y) [] _ h
  rwa [encode_putPair E i j hij] at hh
end MatchingFPRAS.TreeMachine

end OAI
