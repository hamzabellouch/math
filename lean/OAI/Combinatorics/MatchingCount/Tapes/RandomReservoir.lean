import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.RandomWordLaw

namespace OAI

namespace MatchingFPRAS.RandomWord
open Turing BinaryArithmetic

lemma draw_forward_suffix (xs : List (Bool×Bool)) (L R : List Symbol) :
    execute (pairCoins xs) (cfg (some 0) L (List.replicate xs.length 1++3::R))=
      cfg (some 0) ((drawnWord xs).reverse++L) (3::R) := by
  induction xs generalizing L with
  | nil=>rfl
  | cons p xs ih=>
    simp only [pairCoins,List.flatMap_cons,List.length_cons,List.replicate_succ,List.cons_append]
    change execute ([p.1,p.2]++pairCoins xs) (cfg (some 0) L (1::(List.replicate xs.length 1++3::R)))=_
    rw [execute_append,draw_two,ih]
    simp [drawnWord,List.reverse_cons,List.append_assoc]
lemma finish_run_suffix (L R : List Symbol) (hL : ∀ b∈L,b≠0)
    (xs : List Bool) (hx : xs.length=L.length+3) :
    execute xs (cfg (some 0) L (3::R))=cfg none [] (L.reverse++3::R) := by
  obtain ⟨ys,b,rfl⟩ : ∃ ys b,xs=ys++[b] := by
    have hn : xs.reverse≠[] := by
      intro h
      have h' : xs.length=0 := by simpa only [List.length_reverse,List.length_nil] using congrArg List.length h
      omega
    obtain ⟨b,ys,he⟩:=List.exists_cons_of_ne_nil hn
    exact ⟨ys.reverse,b,by have h:=congrArg List.reverse he; simpa using h⟩
  have hy : ys.length=L.length+2 := by simpa using hx
  have he : execute ys (cfg (some 0) L (3::R))=cfg (some 3) [] (L.reverse++3::R) := by
    have hr:=reset_run L R 3 (by decide) hL ys hy
    cases ys with
    | nil=>simp at hy
    | cons c ys=>
      rw [execute_cons] at hr ⊢
      have ht : tick machine (cfg (some 0) L (3::R)) c=tick machine (cfg (some 2) L (3::R)) c := by
        simp [tick,machine,Tape.mk₂,Tape.mk']
      rw [ht]
      exact hr
  rw [execute_append,he]
  simp [execute,tick,machine,cfg]
lemma execute_word_suffix (xs : List (Bool×Bool)) (tail : List Bool) (R : List Symbol)
    (ht : tail.length=xs.length+3) :
    execute (pairCoins xs++tail) (cfg (some 0) [] (List.replicate xs.length 1++3::R))=
      cfg none [] (drawnWord xs++3::R) := by
  rw [execute_append,draw_forward_suffix,List.append_nil]
  have hn : ∀ b∈(drawnWord xs).reverse,b≠0 := by
    intro b hb
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hb)
    exact bitSymbol_ne_zero _
  simpa using finish_run_suffix (drawnWord xs).reverse R hn tail (by simpa [drawnWord] using ht)
lemma run_word_suffix (m : ℕ) (R : List Symbol) (bits : Fin (m*2+(m+3))→Bool) :
    run machine (List.replicate m 1++3::R) bits=
      cfg none [] ((List.ofFn (outputCoins m bits)).map bitSymbol++3::R) := by
  obtain ⟨⟨x,y⟩,rfl⟩:=(wordTapeEquiv m).symm.surjective bits
  change execute (List.ofFn ((wordTapeEquiv m).symm (x,y)))
    (cfg (some 0) [] (List.replicate m 1++3::R))=_
  rw [wordTape_list]
  have h:=execute_word_suffix (List.ofFn x) (List.ofFn y) R (by simp)
  have ho : outputCoins m ((wordTapeEquiv m).symm (x,y))=(fun i=>(x i).1) := by
    funext i
    simp only [outputCoins,Equiv.apply_symm_apply]
  rw [ho]
  simpa only [List.length_ofFn,drawnWord,List.map_ofFn,Function.comp_def] using h
end MatchingFPRAS.RandomWord

end OAI
