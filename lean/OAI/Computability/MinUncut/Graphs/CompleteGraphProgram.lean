import Mathlib
import OAI.Computability.MinUncut.Search.ArithmeticTactic
import OAI.Computability.MinUncut.Graphs.DemandStageEffectivity
import OAI.Computability.MinUncut.Estimates.UniformEquationOutput

namespace OAI

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Target MinUncut.SourceTemplate GraphRegisters

variable {J : ℕ} (P : Parameters J)
  (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))

def graphStageWords (v : List ℕ) : List ℕ :=
  GraphRegisters.renderRaw (demandStageWords
    (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) P.o.t P.denominatorCoefficient v)

def graphStageProgram : PolyProgram (graphStageWords P E) :=
  GraphRegisters.rawRenderer.comp (demandStageProgram
    (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) P.o.t P.denominatorCoefficient)

def completeGraphWords (u D : ℕ) (v : List ℕ) : List ℕ :=
  graphStageWords P E (sourceStageWords u D v)

def completeGraphProgram (u D : ℕ) : PolyProgram (completeGraphWords P E u D) :=
  (graphStageProgram P E).comp (sourceStageProgram u D)

lemma graphStageWords_spec (input : SourceEncoding.Input) (rest : List ℕ) :
    ∃junk,graphStageWords P E (SourceEncoding.inputWords input++rest)=
      let ds := generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
        (rationalSigma J) (rationalEta J)
      ((paddedVariableEncoding input.«variables» P.o.t).size+ds.length*3)::
        ((canonicalTable ds).map Bool.toNat++2::(5*P.denominator (Fin input.equations.length))::junk) := by
  obtain ⟨junk,hj⟩:=demandStageWords_spec P input E rest
  simp only [graphStageWords,hj,GraphRegisters.renderer_pack]
  exact ⟨_,rfl⟩

lemma completeGraphWords_spec (F : Formula) (u D : ℕ) (hD : 0<D) (hne : F.clauses≠[]) :
    ∃junk,completeGraphWords P E u D (MinUncutGames.Foundations.Complexity.formulaWords F)=
      let input:=sourceInput F u D hD
      let ds := generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
        (rationalSigma J) (rationalEta J)
      ((paddedVariableEncoding input.«variables» P.o.t).size+ds.length*3)::
        ((canonicalTable ds).map Bool.toNat++2::(5*P.denominator (Fin input.equations.length))::junk) := by
  obtain ⟨rest,hr⟩:=sourceStageWords_spec F u D hD hne
  simp only [completeGraphWords,hr]
  exact graphStageWords_spec P E _ _

end MinUncut.Costed.SourceWords

namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncut.OuterSmoothness.Density
attribute [local irreducible] selectedInner selectedOuter
open MinUncut.Costed MinUncut.Costed.SourceWords MinUncut.SourceTemplate MinUncut.OuterSmoothness
abbrev chosenM (K : ℕ) := (selectedInner K).m
abbrev chosenN (K : ℕ) := (selectedInner K).n
abbrev chosenT (K : ℕ) := (selectedOuter K).t
abbrev chosenL (K : ℕ) := (selectedOuter K).k
lemma c_chosenM : Computable chosenM := c_innerData_m.comp c_selectedInner
lemma c_chosenN : Computable chosenN := c_innerData_n.comp c_selectedInner
lemma c_chosenT : Computable chosenT := c_outerData_t.comp c_selectedOuter
lemma c_chosenL : Computable chosenL := c_outerData_k.comp c_selectedOuter
lemma chosenN_pos (K : ℕ) : 0<chosenN K := by
  have h := (selectedInner_check K).2.1
  change (selectedInner K).k+2≤chosenN K at h
  omega
lemma out_chosenBudgets : (tests ℕ).Out (fun K j=>rationalBudgets (parameterJ K) (selectedInner K) (selectedOuter K) j) := by
  let q := tests ℕ
  have hc := ca_ratInv (ca_ratCast (computableCard (Face.codes chosenM chosenN c_chosenM c_chosenN chosenN_pos)))
  have first : q.Map bool (fun _ j=>decide (j=Test.first)) :=
    map_fixed_apply SampleEnumeration.tests.encoding Encoding.bool (fun j=>decide (j=Test.first)) (map_id q)
  have second : q.Map bool (fun _ j=>decide (j=Test.second)) :=
    map_fixed_apply SampleEnumeration.tests.encoding Encoding.bool (fun j=>decide (j=Test.second)) (map_id q)
  have third : q.Map bool (fun _ j=>decide (j=Test.third)) :=
    map_fixed_apply SampleEnumeration.tests.encoding Encoding.bool (fun j=>decide (j=Test.third)) (map_id q)
  have h := Out.cond first (out_const q (ca_ratMul (ca_const 10) (c_sigma.comp c_parameterJ)))
    (Out.cond second (out_const q (ca_ratMul (ca_const 10)
      (ca_ratAdd (c_eta.comp c_parameterJ) (c_eta.comp c_parameterJ))))
      (Out.cond third (out_const q hc) (out_const q (c_outerData_b4.comp c_selectedOuter))))
  exact h.ofEq (by intro K j; cases j <;> rfl)
lemma c_chosenAccuracy : Computable (fun K=>tableAccuracy (parameterJ K) (selectedInner K) (selectedOuter K)) := by
  exact ca_ratDiv (ca_const 1) (ca_ratMul (ca_const 8)
    (ca_ratAdd (ca_const 1) (computable_sum out_chosenBudgets.ratInv computable_ratAdd)))

lemma c_chosenGrid : Computable (fun K=>(selectedParameters K).grid) := by
  have hc := c_selectedGrid.comp
    ((computableCard (Grid.coordinates chosenM chosenN c_chosenM c_chosenN chosenN_pos)).pair
      ((computableCard (Grid.indices chosenM chosenN c_chosenM c_chosenN chosenN_pos)).pair
        ((ca_ratAdd (ca_ratMul (ca_const 2) (ca_ratCast (ca_pow c_chosenN c_chosenM))) (ca_const 1)).pair
          c_chosenAccuracy)))
  apply hc.of_eq
  intro K
  exact selectedGrid_eq _ _ _ _ (by positivity) (tableAccuracy_pos (parameterJ_pos K) _ (selectedInner_check K) _ (selectedOuter_check K))

lemma c_chosenRate : Computable (fun K=>rationalRate (parameterJ K) (selectedInner K)) :=
  ca_ratDiv (ca_ratPow (c_eta.comp c_parameterJ) (ca_const 2)) (ca_ratCast c_chosenM)
lemma c_fixedSetCard : Computable (fun K=>Fintype.card (FixedSets (Fin (chosenT K)) (chosenL K))) := by
  let a:=sets chosenT c_chosenT
  let d:∀K,Finset (Fin (chosenT K))→Bool:=fun K S=>decide (S.card=chosenL K)
  have hd : a.Map bool d := ((out_setCard chosenT c_chosenT).pair (out_const a c_chosenL)).map Primrec.eq.computablePred.decide |>.toBool
  have hc := computableCard (a.restrict d hd)
  apply hc.of_eq
  intro K
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun S=>by simp [d]))

lemma c_chosenDenominator : Computable (fun K=>(selectedParameters K).denominatorCoefficient) := by
  exact ca_mul (ca_mul c_fixedSetCard (ca_pow (ca_const 3) c_chosenT))
    (Denominator.c_innerDenominator chosenT chosenM chosenN c_chosenT c_chosenM c_chosenN chosenN_pos
      (fun K=>(selectedParameters K).grid) c_chosenGrid
      _ c_chosenRate _ out_chosenBudgets)

def chosenEnumeration (K : ℕ) :=
  DemandOrder.enumeration (chosenT K) (chosenL K) (chosenM K) (chosenN K) (chosenN_pos K) (selectedParameters K).grid
lemma c_chosenExpressions : Computable (fun K=>(localExpressions (chosenEnumeration K)
    (rationalRate (parameterJ K) (selectedInner K))
    (rationalBudgets (parameterJ K) (selectedInner K) (selectedOuter K))
    (rationalSigma (parameterJ K)) (rationalEta (parameterJ K))).map (fun e=>e.program.code)) :=
  DemandOrder.c_localExpressions chosenT chosenL c_chosenT c_chosenL chosenM chosenN
    c_chosenM c_chosenN chosenN_pos _ c_chosenGrid _ c_chosenRate _ out_chosenBudgets
    _ _ (c_sigma.comp c_parameterJ) (c_eta.comp c_parameterJ)

lemma c_completeGraphCode (u D : ℕ) : Computable (fun K=>
    (completeGraphProgram (selectedParameters K) (chosenEnumeration K) u D).code) := by
  have hd := Syntax.c_demandStageCode _ c_chosenExpressions chosenT
    (fun K=>(selectedParameters K).denominatorCoefficient) c_chosenT c_chosenDenominator
  exact MinUncut.CodeEffective.computable_comp.comp
    (MinUncut.CodeEffective.computable_comp.comp (ca_const GraphRegisters.rawRenderer.code) hd)
    (ca_const (sourceStageProgram u D).code)
end MinUncut.Preprocess

end

end OAI
