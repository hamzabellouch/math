import Mathlib
import OAI.Computability.MinUncut.Graphs.GraphSize
import OAI.Computability.MinUncut.Estimates.BlocksEffectivity

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords MinUncut.CodeEffective
lemma c_tupleCountExpr : C tupleCountExpr := (C.fixed (.reg 1)).pow Computable.id
lemma c_variableCountExpr : C variableCountExpr := by
  exact ((((C.fixed (.reg 0)).pow (ca_const 3)).mul (C.fixed (.const 2))).pow Computable.id |>.add
    (((C.fixed (.reg 0)).add (((C.fixed (.reg 0)).pow (ca_const 3)).mul
      (C.fixed (.const 2)))).pow Computable.id)).mul
      (C.const (ca_pow (ca_const 2) (ca_pow (ca_const (2^3)) Computable.id)))
lemma c_demandStageCode {P : Type} [Primcodable P] (es : P → List AExpr)
    (he : Computable (fun p=>(es p).map (fun e=>e.program.code)))
    (t D : P → ℕ) (ht : Computable t) (hD : Computable D) :
    Computable (fun p=>(demandStageProgram (es p) (t p) (D p)).code) := by
  have hl : Computable (fun p=>(es p).length) :=
    (Computable.list_length.comp he).of_eq (fun p=>List.length_map ..)
  have hv := c_variableCountExpr.precomp ht
  have hu : C (fun p=>unitCountExpr (es p) (t p)) :=
    ((c_tupleCountExpr.precomp ht).mul (C.const hl)).div (C.fixed (.const 3))
  have hk : C (fun p=>thresholdExpr (t p) (D p)) :=
    (C.const (ca_mul (ca_const 5) hD)).mul (c_tupleCountExpr.precomp ht)
  have hf := p_forwardCode.to_comp.comp he (c_tupleCountExpr.precomp ht)
  apply (computable_cons.comp hv (computable_cons.comp hu (computable_cons.comp hk hf))).of_eq
  intro p
  rw [forwardCode_eq]
  rfl
end MinUncut.Preprocess.Syntax

end
end

end OAI
