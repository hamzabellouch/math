import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryIncrement
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryCopy

namespace OAI

namespace MatchingFPRAS.RandomWord
open Turing BinaryArithmetic

abbrev machine : RandomMachine where
  states := 3
  transition s a b :=
    if s=0 then
      if a=3 then some (2,.move .left) else some (1,.write (bitSymbol b))
    else if s=1 then some (0,.move .right)
    else if s=2 then
      if a=0 then some (3,.move .right) else some (2,.move .left)
    else none
abbrev cfg (s : Option (Fin 4)) (L R : List Symbol) : Configuration machine :=
  ⟨s,Tape.mk₂ L R⟩
def execute (xs : List Bool) (c : Configuration machine) : Configuration machine :=
  xs.foldl (tick machine) c
lemma execute_append (xs ys : List Bool) (c : Configuration machine) :
    execute (xs++ys) c=execute ys (execute xs c) := List.foldl_append
lemma execute_cons (b : Bool) (xs : List Bool) (c : Configuration machine) :
    execute (b::xs) c=execute xs (tick machine c b) := rfl
lemma execute_halted (xs : List Bool) (L R : List Symbol) :
    execute xs (cfg none L R)=cfg none L R := by
  induction xs with
  | nil => rfl
  | cons b xs ih => exact ih
lemma draw_two (b c : Bool) (L R : List Symbol) :
    execute [b,c] (cfg (some 0) L (1::R))=cfg (some 0) (bitSymbol b::L) R := by
  simp [execute,tick,machine,cfg,Tape.mk₂,Tape.mk',Tape.write,Tape.move]
def pairCoins (xs : List (Bool×Bool)) : List Bool := xs.flatMap (fun p=>[p.1,p.2])
def drawnWord (xs : List (Bool×Bool)) : List Symbol := xs.map (fun p=>bitSymbol p.1)
lemma draw_forward (xs : List (Bool×Bool)) (L : List Symbol) :
    execute (pairCoins xs) (cfg (some 0) L (List.replicate xs.length 1++[3]))=
      cfg (some 0) ((drawnWord xs).reverse++L) [3] := by
  induction xs generalizing L with
  | nil => rfl
  | cons p xs ih =>
    simp only [pairCoins,List.flatMap_cons,List.length_cons,List.replicate_succ,List.cons_append]
    change execute ([p.1,p.2]++pairCoins xs) (cfg (some 0) L (1::(List.replicate xs.length 1++[3])))=_
    rw [execute_append,draw_two]
    rw [ih]
    simp [drawnWord,List.reverse_cons,List.append_assoc]
lemma reset_tick (L R : List Symbol) (a : Symbol) (ha : a≠0) (b : Bool) :
    tick machine (cfg (some 2) L (a::R)) b=
      ⟨some 2,(Tape.mk₂ L (a::R)).move .left⟩ := by
  simp [tick,machine,Tape.mk₂,Tape.mk',ha]
lemma reset_run (L R : List Symbol) (a : Symbol) (ha : a≠0)
    (hL : ∀ b∈L,b≠0) (xs : List Bool) (hx : xs.length=L.length+2) :
    execute xs (cfg (some 2) L (a::R))=cfg (some 3) [] (L.reverse++a::R) := by
  induction L generalizing a R xs with
  | nil =>
    obtain ⟨b,c,rfl⟩ : ∃ b c,xs=[b,c] := by
      exact List.length_eq_two.mp (by simpa using hx)
    rw [execute_cons,reset_tick _ _ _ ha]
    simp [execute,tick,machine,cfg,Tape.mk₂,Tape.mk',Tape.move,ListBlank.cons_mk]
    apply Quotient.sound
    exact Or.inr ⟨1,rfl⟩
  | cons b L ih =>
    cases xs with
    | nil => simp at hx
    | cons c xs =>
      have hb : b≠0:=hL b (by simp)
      have hL' : ∀ d∈L,d≠0:=fun d hd=>hL d (by simp [hd])
      rw [execute_cons,reset_tick _ _ _ ha]
      have ht : (⟨some 2,(Tape.mk₂ (b::L) (a::R)).move .left⟩ : Configuration machine)=
          cfg (some 2) L (b::a::R) := by
        simp [cfg,Tape.mk₂,Tape.mk',Tape.move]
      rw [ht,ih (a::R) b hb hL' xs (by simpa using hx)]
      simp [cfg,List.reverse_cons,List.append_assoc]
lemma finish_run (L : List Symbol) (hL : ∀ b∈L,b≠0)
    (xs : List Bool) (hx : xs.length=L.length+3) :
    execute xs (cfg (some 0) L [3])=cfg none [] (L.reverse++[3]) := by
  obtain ⟨ys,b,rfl⟩ : ∃ ys b,xs=ys++[b] := by
    have hn : xs.reverse≠[] := by
      intro h
      have h' : xs.length=0 := by simpa only [List.length_reverse,List.length_nil] using congrArg List.length h
      omega
    obtain ⟨b,ys,he⟩:=List.exists_cons_of_ne_nil hn
    exact ⟨ys.reverse,b,by have h:=congrArg List.reverse he; simpa using h⟩
  have hy : ys.length=L.length+2 := by simpa using hx
  have he : execute ys (cfg (some 0) L [3])=cfg (some 3) [] (L.reverse++[3]) := by
    have hr:=reset_run L [] 3 (by decide) hL ys hy
    cases ys with
    | nil => simp at hy
    | cons c ys =>
      rw [execute_cons] at hr ⊢
      have ht : tick machine (cfg (some 0) L [3]) c=tick machine (cfg (some 2) L [3]) c := by
        simp [tick,machine,Tape.mk₂,Tape.mk']
      rw [ht]
      exact hr
  rw [execute_append,he]
  simp [execute,tick,machine,cfg]

theorem execute_word (xs : List (Bool×Bool)) (tail : List Bool)
    (ht : tail.length=xs.length+3) :
    execute (pairCoins xs++tail) (cfg (some 0) [] (List.replicate xs.length 1++[3]))=
      cfg none [] (drawnWord xs++[3]) := by
  rw [execute_append,draw_forward,List.append_nil]
  have hn : ∀ b∈(drawnWord xs).reverse,b≠0 := by
    intro b hb
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hb)
    exact bitSymbol_ne_zero _
  simpa using finish_run (drawnWord xs).reverse hn tail (by simpa [drawnWord] using ht)
end MatchingFPRAS.RandomWord

end OAI
