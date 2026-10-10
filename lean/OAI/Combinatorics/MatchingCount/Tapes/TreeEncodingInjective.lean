import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeProgramUnique

namespace OAI

namespace MatchingFPRAS.TreeData
lemma encode_prefix_injective (a : Data) : ∀ b xs ys,
    encode a++xs=encode b++ys → a=b ∧ xs=ys := by
  induction a with
  | nil=>
    intro b xs ys h
    cases b with
    | nil=>simpa [encode] using h
    | cons b c=>simp [encode] at h
  | cons a c ia ic=>
    intro b xs ys h
    cases b with
    | nil=>simp [encode] at h
    | cons b d=>
      simp only [encode,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      obtain ⟨hab,he⟩:=ia b _ _ h
      obtain ⟨hcd,hxy⟩:=ic d xs ys he
      exact ⟨congrArg₂ Data.cons hab hcd,hxy⟩
lemma encode_injective : Function.Injective encode := by
  intro a b h
  exact (encode_prefix_injective a b [] [] (by simpa using h)).1
lemma ofList_injective : Function.Injective ofList := by
  intro a
  induction a with
  | nil=>intro b h; cases b <;> simp_all [ofList]
  | cons a as ih=>
    intro b h
    cases b with
    | nil=>simp [ofList] at h
    | cons b bs=>
      obtain ⟨rfl,he⟩:=Data.cons.inj h
      rw [ih he]
lemma bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]
lemma nat_injective : Function.Injective nat := by
  intro a b h
  have hh: a.bits=b.bits:=(List.map_injective_iff.mpr bit_injective) (ofList_injective h)
  have := congrArg StackAddition.value hh
  simpa only [StackAddition.value_bits] using this
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma sameProgram_encode {f : A→B} {g : C→D} (F : Realizer f) (G : Realizer g)
    (h : F.program=G.program) (a : A) (b : C) (hi : TreeTyped.encode a=TreeTyped.encode b) :
    TreeTyped.encode (f a)=TreeTyped.encode (g b) := by
  have hf:=F.correct a .nil
  have hg:=G.correct b .nil
  change Exec F.program (inputStacks a) (inputStacks (f a)) _ at hf
  change Exec G.program (inputStacks b) (inputStacks (g b)) _ at hg
  rw [h,stacks_eq_of_encode hi] at hf
  exact TreeData.encode_injective (congrFun (hf.unique hg) (.inl 0))
end MatchingFPRAS.TreePost

namespace MatchingFPRAS.TreeTyped
open TreeData

lemma list_encode_injective {A : Type} [Codec A] (hf : Function.Injective (encode (A:=A))) :
    Function.Injective (encode (A:=List A)) := by
  intro a b h
  exact (List.map_injective_iff.mpr hf) (ofList_injective h)
lemma nat_encode_injective : Function.Injective (encode (A:=ℕ)) := TreeData.nat_injective
lemma finsetNat_encode_injective : Function.Injective (encode (A:=Finset ℕ)) := by
  intro a b h
  change encode (a.sort (·≤·))=encode (b.sort (·≤·)) at h
  have hh:=list_encode_injective nat_encode_injective h
  have := congrArg List.toFinset hh
  simpa using this
lemma pair_encode_injective {A B : Type} [Codec A] [Codec B]
    (ha : Function.Injective (encode (A:=A))) (hb : Function.Injective (encode (A:=B))) :
    Function.Injective (encode (A:=A×B)) := by
  intro a b h
  exact Prod.ext (ha (TreeData.Data.cons.inj h).1) (hb (TreeData.Data.cons.inj h).2)
end MatchingFPRAS.TreeTyped

end OAI
