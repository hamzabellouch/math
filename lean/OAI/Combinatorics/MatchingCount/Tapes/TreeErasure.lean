import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptions
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData

variable {A B : Type} [Codec A] [Codec B]
lemma constantData_program (d : Data) :
    (constantData (A:=A) d).program=(constantData (A:=B) d).program := by
  induction d with
  | nil=>rfl
  | cons a b ih ihb=>
    change TreeFunction.pair _ _ = TreeFunction.pair _ _
    rw [ih,ihb]
lemma constant_program (a : A) (b : B) (h : encode a=encode b)
    {C D : Type} [Codec C] [Codec D] :
    (constant (A:=C) a).program=(constant (A:=D) b).program := by
  change (constantData (A:=C) (encode a)).program=(constantData (A:=D) (encode b)).program
  rw [h]
  exact constantData_program _
lemma encode_empty_finset {E : Type} [Codec E] [LinearOrder E] :
    encode (∅ : Finset E)=Data.nil := by
  simp only [encode_finset,Finset.sort_empty,encode_list_nil]
lemma head_program (a : A) (b : B) (h : encode a=encode b) :
    (head a).program=(head b).program := by
  change RegisterStructured.select 0 (constant a).program first.program =
    RegisterStructured.select 0 (constant b).program first.program
  rw [constant_program a b h (C:=List A) (D:=List B)]
  rfl
lemma getDFast_program (a : A) (b : B) (h : encode a=encode b) :
    (getDFast a).program=(getDFast b).program := by
  change RegisterProc.seq dropFast.program (head a).program =
    RegisterProc.seq dropFast.program (head b).program
  rw [head_program a b h]
  rfl
lemma draw_program (a : A) (b : B) (h : encode a=encode b) :
    (ExecutableOptions.drawRealizer a).program=(ExecutableOptions.drawRealizer b).program := by
  unfold ExecutableOptions.drawRealizer
  dsimp only [Realizer.congr, composition, pair]
  rw [getDFast_program a b h]
  rfl
end MatchingFPRAS.TreeTyped

end OAI
