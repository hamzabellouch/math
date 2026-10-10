import Mathlib
import OAI.Computability.MinUncut.Estimates.ExpressionEffectivity
import OAI.Computability.MinUncut.Estimates.ReversePrefixProgram

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec

def prefCode (cs : List Code) : Code :=
  cs.foldr (fun c b=>.cons (.comp c Blocks.extractor.code) b) (PolyProgram.drop 2).code
lemma p_prefCode : Primrec prefCode :=
  Primrec.list_foldr Primrec.id (Primrec.const _)
    (primrec_cons.comp
      (primrec_comp.comp (Primrec.fst.comp Primrec.snd) (Primrec.const _))
      (Primrec.snd.comp Primrec.snd)).to₂

def stepCode (cs : List Code) : Code :=
  .cons PolyProgram.succ.code
    (.cons (bin PolyProgram.add.code (PolyProgram.projection 1).code (constCode cs.length)) (prefCode cs))
lemma p_stepCode : Primrec stepCode :=
  primrec_cons.comp (Primrec.const _)
    (primrec_cons.comp
      ((p_bin _).comp (Primrec.const _) (p_constCode.comp Primrec.list_length)) p_prefCode)
lemma prefCode_eq (es : List AExpr) : prefCode (es.map (fun e=>e.program.code)) =
    (Blocks.stepProgram.go es).code := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [prefCode,List.map_cons,List.foldr_cons] at *; rw [ih]; rfl
lemma stepCode_eq (es : List AExpr) : stepCode (es.map (fun e=>e.program.code))=(Blocks.stepProgram es).code := by
  simp only [stepCode,List.length_map,prefCode_eq]
  rfl
lemma p_iterCode : Primrec iterCode := by
  exact primrec_fix.comp (primrec_case.comp (Primrec.const _)
    (primrec_cons.comp (Primrec.const _)
      (primrec_cons.comp (Primrec.const _) (primrec_comp.comp Primrec.id (Primrec.const _)))))
def forwardCode (cs : List Code) (N : Code) : Code :=
  .comp reversePrefixProgram.code (.comp PolyProgram.tail.code
    (.comp (iterCode (stepCode cs.reverse))
      (.cons N (.cons (constCode 0) (.cons (constCode 0) Code.id)))))
lemma p_forwardCode : Primrec₂ forwardCode := by
  exact primrec_comp.comp (Primrec.const _)
    (primrec_comp.comp (Primrec.const _)
      (primrec_comp.comp (p_iterCode.comp (p_stepCode.comp (Primrec.list_reverse.comp Primrec.fst)))
        (primrec_cons.comp Primrec.snd (Primrec.const _))))
lemma forwardCode_eq (es : List AExpr) (N : AExpr) :
    forwardCode (es.map (fun e=>e.program.code)) N.program.code=(Blocks.forward es N).code := by
  unfold forwardCode
  rw [←List.map_reverse,stepCode_eq]
  rfl
end MinUncut.Preprocess.Syntax

end
end

end OAI
