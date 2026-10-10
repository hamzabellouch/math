import Mathlib
import OAI.Computability.MinUncut.Graphs.CompleteGraphProgram
import OAI.Computability.MinUncut.Graphs.Graph

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
attribute [local irreducible] selectedInner selectedOuter
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Hastad
open MinUncutGames.Integration.SourceParameters MinUncut.Costed.SourceWords MinUncut.SourceTemplate
def chosenError (K : ℕ) := (selectedParameters K).sourceError
def chosenNoise (K : ℕ) := SourceNoiseParameter.noiseDenominator (chosenError K)
def chosenRepetition (K : ℕ) :=
  SourceGap.repetitionCount PCP.PCPIteration.finalClauseGap (chosenError K)
    PCP.PCPIteration.finalClauseGap_positive PCP.TableGapReduction.finalClauseGap_le_one
    (selectedParameters K).sourceError_pos (chosenNoise K) (SourceNoiseParameter.noiseDenominator_pos _)
lemma c_chosenError : Computable chosenError := by
  have hd := ca_ratDiv (c_outerData_b4.comp c_selectedOuter) (ca_ratCast c_chosenT)
  have hp:=ca_ratLe (ca_const (1/2:ℚ)) hd
  exact (Computable.cond hp.decide (ca_const (1/2:ℚ)) hd).of_eq (by intro K; simp [chosenError,Outer.Parameters.sourceError,min_def,selectedParameters,chosenT])
lemma c_chosenNoise : Computable chosenNoise := by
  exact ca_add (primrec_ratDen.to_comp.comp c_chosenError) (ca_const 2)
lemma c_chosenRepetition : Computable chosenRepetition := by
  apply Computable.find
  exact ca_and (ca_natLt (ca_const 0) Computable.snd)
    (ca_ratLt (ca_ratPow (ca_const (rate (PCP.PCPIteration.finalClauseGap/3))) Computable.snd)
      (ca_ratMul (ca_ratMul (ca_const 4) (ca_ratInv (ca_ratCast (c_chosenNoise.comp Computable.fst))))
        (ca_ratPow (c_chosenError.comp Computable.fst) (ca_const 2))))
attribute [local irreducible] chosenRepetition chosenNoise sourceStageProgram
lemma c_selectedGraphCode : Computable (fun K=>
    (completeGraphProgram (selectedParameters K) (chosenEnumeration K) (chosenRepetition K) (chosenNoise K)).code) := by
  have hd := Syntax.c_demandStageCode _ c_chosenExpressions chosenT
    (fun K=>(selectedParameters K).denominatorCoefficient) c_chosenT c_chosenDenominator
  have hs := Syntax.c_sourceStageCode.comp (c_chosenRepetition.pair c_chosenNoise)
  have hc : Computable (fun K => Turing.ToPartrec.Code.comp
      (Turing.ToPartrec.Code.comp MinUncut.Costed.GraphRegisters.rawRenderer.code
        (demandStageProgram
          (localExpressions (chosenEnumeration K)
            (rationalRate (parameterJ K) (selectedInner K))
            (rationalBudgets (parameterJ K) (selectedInner K) (selectedOuter K))
            (rationalSigma (parameterJ K)) (rationalEta (parameterJ K)))
          (chosenT K) (selectedParameters K).denominatorCoefficient).code)
      (sourceStageProgram (chosenRepetition K) (chosenNoise K)).code) :=
    MinUncut.CodeEffective.computable_comp.comp
      (MinUncut.CodeEffective.computable_comp.comp (ca_const MinUncut.Costed.GraphRegisters.rawRenderer.code) hd) hs
  apply hc.of_eq
  intro K
  rfl
end MinUncut.Preprocess

end
end

end OAI
