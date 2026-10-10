import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeEncodingInjective
import OAI.Combinatorics.MatchingCount.Tapes.BlockMap
import OAI.Combinatorics.MatchingCount.Tapes.Packed

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreePost

lemma symbol_encode_injective : Function.Injective (TreeTyped.encode (A:=Symbol)) := by
  intro a b h
  have hh : TreeTyped.encode (LiteralCodec.parts a)=TreeTyped.encode (LiteralCodec.parts b) := h
  have he := (TreeData.Data.cons.inj hh).1
  have hs : (LiteralCodec.parts a).1=(LiteralCodec.parts b).1 :=
    list_encode_injective (show Function.Injective (TreeTyped.encode (A:=Bool)) from bit_injective) he
  apply Fin.ext
  simpa only [LiteralCodec.parts,List.length_replicate] using congrArg List.length hs
lemma symbolBits_injective : Function.Injective symbolBits := by
  intro a b h
  have h1:=List.append_cancel_right (show _++[true]=_++[true] from h)
  exact symbol_encode_injective (TreeData.encode_injective (List.reverse_injective h1))
lemma encoding_injective (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    Function.Injective (fun a : Γ=>(FixedEncoding.enc Γ a).toList.map BoolPostCompiler.up) := by
  intro a b h
  have hb : (FixedEncoding.enc Γ a).toList=(FixedEncoding.enc Γ b).toList :=
    List.map_injective_iff.mpr (Function.LeftInverse.injective BoolPostCompiler.down_up) h
  exact FixedEncoding.injective Γ (Subtype.ext hb)
lemma block_injective : Function.Injective block := encoding_injective Alphabet
lemma flatMap_injective_fixed {A B : Type} (f : A→List B) (w : ℕ) (hw : 0<w)
    (hl : ∀ a,(f a).length=w) (hi : Function.Injective f) : Function.Injective (List.flatMap f) := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons b bs => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
    | cons b bs =>
      have h1 := List.append_inj_left h ((hl a).trans (hl b).symm)
      have h2 := List.append_inj_right h ((hl a).trans (hl b).symm)
      exact congrArg₂ List.cons (hi h1) (ih h2)
lemma width_pos : 0<width := Fintype.card_pos
lemma letter_injective : Function.Injective letter := by
  intro a b h
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h
  simpa only [letter,bitRow,ite_true,Option.some.injEq] using hh
lemma chunk_injective : Function.Injective chunk := by
  intro a b h
  have hi : Function.Injective (fun b=>block (letter b)) := by
    intro b c he
    exact letter_injective (block_injective he)
  have hh : (symbolBits a).flatMap (fun b=>block (letter b)) =
      (symbolBits b).flatMap (fun b=>block (letter b)) := h
  exact symbolBits_injective (flatMap_injective_fixed (fun b=>block (letter b)) width width_pos
    (fun b=>block_length (letter b)) hi hh)
lemma encoding_blank (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    (FixedEncoding.enc Γ default).toList.map BoolPostCompiler.up=
      List.replicate (Fintype.card Γ) (0:Symbol) := by
  rw [FixedEncoding.blank]
  change (List.replicate (Fintype.card Γ) false).map _ = _
  rw [List.map_replicate]
  rfl
lemma block_blank : block default=List.replicate width 0 := encoding_blank Alphabet
lemma block_ne_zero (a : Alphabet) (ha : a≠default) : block a≠List.replicate width 0 := by
  intro he
  exact ha (block_injective (he.trans block_blank.symm))
lemma chunk_nonzero (a : Symbol) : ∃ s∈chunk a,s≠0 := by
  classical
  by_contra h
  push Not at h
  have h1 : ∀ s∈block (letter true),s=(0:Symbol) := by
    intro s hs
    exact h s (List.mem_flatMap.mpr ⟨true,by simp [symbolBits],hs⟩)
  have he : block (letter true)=List.replicate width 0 := by
    rw [←block_length (letter true)]
    exact List.eq_replicate_of_mem h1
  apply block_ne_zero (letter true) _ he
  intro h2
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h2
  change (some true : Option Bool)=none at hh
  exact Option.some_ne_none true hh
noncomputable def chunkFn (a : Symbol) : LiteralBlockMap.Block (18*width) :=
  fun i=>(chunk a)[i.val]'(by rw [chunk_length];exact i.isLt)
lemma chunkFn_word (a : Symbol) : List.ofFn (chunkFn a)=chunk a := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,chunk_length]
  · intro i hi hj; simp only [List.getElem_ofFn,chunkFn]
noncomputable def unchunk (b : LiteralBlockMap.Block (18*width)) : List Symbol :=
  [Function.invFun chunk (List.ofFn b)]
lemma unchunk_chunkFn (a : Symbol) : unchunk (chunkFn a)=[a] := by
  rw [unchunk,chunkFn_word,Function.leftInverse_invFun chunk_injective]
lemma chunkFn_nonzero (a : Symbol) : chunkFn a≠fun _=>0 := by
  intro he
  have hh:=congrArg List.ofFn he
  rw [chunkFn_word,List.ofFn_const] at hh
  obtain ⟨s,hs,hn⟩:=chunk_nonzero a
  rw [hh] at hs
  exact hn (List.eq_of_mem_replicate hs)
end MatchingFPRAS.LiteralPacked

end OAI
