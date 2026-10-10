import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeErasure

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma program_congr {f g : A→B} (F : Realizer f) (h : ∀ a,f a=g a) : (F.congr h).program=F.program := rfl
lemma program_recode {f : C→D} (F : Realizer f) (i : A→C) (g : A→B) (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a)) : (F.recode i g hi ho).program=F.program := rfl
lemma program_composition {f : A→B} {g : B→C} (F : Realizer f) (G : Realizer g) :
  (composition F G).program=RegisterProc.seq F.program G.program := rfl
lemma program_pair {f : A→B} {g : A→C} (F : Realizer f) (G : Realizer g) :
  (pair F G).program=TreeFunction.pair F.program G.program := rfl
lemma program_fold {f : A×B→B} (F : Realizer f) :
  (fold F).program=RegisterControl.compile (Fold.code F.program) := rfl
lemma program_choose {f : A→Bool} {g h : A→B} (F : Realizer f) (G : Realizer g) (H : Realizer h) :
  (choose F G H).program=RegisterProc.seq (TreeFunction.copy 0 1 (by decide))
    (RegisterProc.seq (TreeFunction.cons 1 2 (by decide)) (RegisterProc.seq F.program
    (RegisterStructured.select 0 (RegisterProc.seq (TreeFunction.split 0 2 (by decide)) H.program)
      (RegisterProc.seq (TreeFunction.split 0 2 (by decide)) G.program)))) := rfl
lemma program_constant (a : B) : (constant (A:=A) a).program=(constantData (A:=TreeData.Data) (encode a)).program := constantData_program _
end MatchingFPRAS.TreeTyped

end OAI
