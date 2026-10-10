import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.PackedInverse

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open Turing LiteralTape LiteralBlockMap

noncomputable def packCode := LiteralBlockMap.code 1 (fun b=>chunk (b 0)) header
def singletonBlock (a : Symbol) : Block 1 := fun _=>a
lemma singletonBlock_word (a : Symbol) : List.ofFn (singletonBlock a)=[a] := by simp [singletonBlock,List.ofFn_succ]
lemma pack_exec (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    Exec packCode ⟨some .start,(fun _=>0),Tape.mk₁ as⟩
      ⟨none,(fun _=>0),Tape.mk₁ (TreePost.packed as)⟩
      (1+LiteralBlockMap.budget 1 (18*width) as.length 0) := by
  have h:=LiteralBlockMap.computes 1 (fun b=>chunk (b 0)) header (by decide)
    (as.map singletonBlock) (18*width) ?_ ?_ ?_
  · simpa only [packCode,List.flatMap_map,singletonBlock_word,List.flatMap_singleton,List.flatMap_singleton',List.length_map,
      ←List.map_reverse,singletonBlock,←packed_eq] using h
  · intro b hb
    obtain ⟨a,ha',rfl⟩:=List.mem_map.mp hb
    intro he
    exact ha a ha' (congrFun he 0)
  · intro b _ a had
    exact chunk_alphabet _ _ had
  · intro b _
    exact (chunk_length _).le
noncomputable def unpackCode := LiteralBlockMap.code (18*width) unchunk []
lemma unpack_exec (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    Exec unpackCode ⟨some .start,(fun _=>0),Tape.mk₁ (as.reverse.flatMap chunk)⟩
      ⟨none,(fun _=>0),Tape.mk₁ as⟩
      (1+LiteralBlockMap.budget (18*width) 1 as.length 0) := by
  have h:=LiteralBlockMap.computes (18*width) unchunk [] (Nat.mul_pos (by decide) width_pos)
    (as.reverse.map chunkFn) 1 ?_ ?_ ?_
  · simpa only [unpackCode,List.flatMap_map,chunkFn_word,←List.map_reverse,List.reverse_reverse,
      unchunk_chunkFn,List.flatMap_singleton,List.flatMap_singleton',List.nil_append,List.length_map,List.length_reverse] using h
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    exact chunkFn_nonzero a
  · intro b hb a had
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn,List.mem_singleton] at had
    subst a
    exact ha c (List.mem_reverse.mp hc)
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn];rfl
end MatchingFPRAS.LiteralPacked

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
def eraseRight (n : ℕ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  Nat.rec q (fun _ tail=>.write (fun _ _=>default) (.move .right tail)) n
lemma eraseRight_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseRight xs.length q) v (Tape.mk₂ L (xs++R))=
      TM1.stepAux q v (Tape.mk₂ (List.replicate xs.length default++L) R) := by
  induction xs generalizing L with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseRight,TM1.stepAux,List.cons_append,mk₂_write,mk₂_right]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.write (fun _ _=>default) (.move .right tail)) xs.length=eraseRight xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
noncomputable def eraseCode (n : ℕ) : Unit→TM1.Stmt Symbol Unit Unit := fun _=>eraseRight n .halt
lemma erase_exec (xs R : List Symbol) :
    Exec (eraseCode xs.length) ⟨some (),(),Tape.mk₁ (xs++R)⟩ ⟨none,(),Tape.mk₁ R⟩ 1 := by
  have h:=Exec.step (eraseCode xs.length) () () (Tape.mk₁ (xs++R))
  change Exec _ _ (TM1.stepAux (eraseRight xs.length .halt) () (Tape.mk₂ [] (xs++R))) 1 at h
  rw [eraseRight_step] at h
  have he : Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R=Tape.mk₁ R := by
    simp only [List.append_nil,Tape.mk₂,Tape.mk₁]
    rw [show (ListBlank.mk (List.replicate xs.length (0:Symbol)))=ListBlank.mk [] from blank_zero xs.length]
  change Exec _ _ (TM1.stepAux (.halt : TM1.Stmt Symbol Unit Unit) () (Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R)) 1 at h
  simpa only [TM1.stepAux,he] using h
end MatchingFPRAS.LiteralTape

end OAI
