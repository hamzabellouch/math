import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformOutput
import OAI.Computability.MinUncut.Graphs.CanonicalSamplerGraph
import OAI.Computability.MinUncut.Estimates.BlocksEffectivity

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncutGames.Reduction.CloneGap
variable {P : Type} [Primcodable P] {A B : P → Type} {X : Type} [Primcodable X]
lemma out_elimSum {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,A p → X} {g : ∀p,B p → X}
    (hf : a.Out f) (hg : b.Out g) :
    (a.sum b).Out (fun p x=>Sum.elim (f p) (g p) x) := by
  obtain ⟨f',hfr,hf⟩:=hf
  obtain ⟨g',hgr,hg⟩:=hg
  let sz : P × ℕ → ℕ := fun p=>(a.enc p.1).size
  have hs : Computable sz := a.computableSize.comp Computable.fst
  let raw : P × ℕ → X := fun x=>if x.2<sz x then f' x else g' (x.1,x.2-sz x)
  refine ⟨raw,?_,?_⟩
  · exact (Computable.cond (ca_natLt Computable.snd hs).decide hfr
      (hgr.comp (Computable.fst.pair (ca_sub Computable.snd hs)))).of_eq
        (by intro p; simp only [raw,Bool.cond_eq_ite,decide_eq_true_eq])
  · intro p x
    cases x with
    | inl x =>
      change (if ((a.enc p).code x).val<(a.enc p).size then _ else _)=_
      rw [ite_eq_left ((a.enc p).code x).isLt]
      change f' (p,((a.enc p).code x).val)=f p x
      exact hf p x
    | inr x =>
      change (if (a.enc p).size+((b.enc p).code x).val<(a.enc p).size then _ else _)=_
      rw [ite_eq_right (by omega)]
      change g' (p,(a.enc p).size+((b.enc p).code x).val-(a.enc p).size)=_
      rw [Nat.add_sub_cancel_left,hg]
      rfl
lemma map_eqTuple (a : UEncoding P A) : a.equation.Map (a.prod (a.prod (a.prod bool)))
    (fun p e=>equationEquiv (A p) e) := map_to _ (fun p=>equationEquiv (A p))
lemma map_eqFirst (a : UEncoding P A) : a.equation.Map a (fun _ e=>e.first) := by
  have hh := map_comp (map_eqTuple a) (map_fst a (a.prod (a.prod bool)))
  exact hh
lemma map_eqSecond (a : UEncoding P A) : a.equation.Map a (fun _ e=>e.second) := by
  have hh := map_comp (map_eqTuple a) (map_snd a (a.prod (a.prod bool)))
  have hh := map_comp hh (map_fst a (a.prod bool))
  exact hh
lemma map_eqThird (a : UEncoding P A) : a.equation.Map a (fun _ e=>e.third) := by
  have hh := map_comp (map_eqTuple a) (map_snd a (a.prod (a.prod bool)))
  have hh := map_comp hh (map_snd a (a.prod bool))
  have hh := map_comp hh (map_fst a bool)
  exact hh
lemma map_eqRhs (a : UEncoding P A) : a.equation.Map bool (fun _ e=>e.rhs) := by
  have hh := map_comp (map_eqTuple a) (map_snd a (a.prod (a.prod bool)))
  have hh := map_comp hh (map_snd a (a.prod bool))
  have hh := map_comp hh (map_snd a bool)
  exact hh
end MinUncut.Preprocess.UEncoding
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncut.SourceTemplate UEncoding
lemma out_keyTag : keys.Out (fun _ x=>keyTag x) := by
  apply (out_elimSum (out_const fc (Computable.const 0))
    (out_elimSum (out_const gc (Computable.const 1)) (out_const (fixed Encoding.unit) (Computable.const 2)))).ofEq
  intro p x
  cases x with
  | inl _=> rfl
  | inr x=>cases x <;> rfl
lemma out_keyTable : keys.Out (fun _ x=>keyTable x) := by
  apply (out_elimSum (out_code fc)
    (out_elimSum (out_code gc) (out_const (fixed Encoding.unit) (Computable.const 0)))).ofEq
  intro p x
  cases x with
  | inl _=> rfl
  | inr x=>cases x <;> rfl
end MinUncut.Preprocess.Source

end
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction MinUncut.Costed
noncomputable section

def sourceExpressions (u D : ℕ) : List AExpr :=
  (slotContextEncoding u).enumerate.flatMap (fun s=>
    (testTapeEncoding u D).enumerate.flatMap (equationExpressions s))

lemma sourceExpressions_eval (F : Formula) {u D : ℕ} (c : ClauseContext F u) :
    (sourceExpressions u D).map (fun e=>e.eval (inputTuple F c))=
      (slotContextEncoding u).enumerate.flatMap (fun s=>
        (testTapeEncoding u D).enumerate.flatMap (fun t=>
          SourceEncoding.equationWords (sourceEquation F u D ((c,s),t)))) := by
  simp only [sourceExpressions,List.map_flatMap,equationExpressions_eval]

lemma emitted_source (F : Formula) (u D : ℕ) :
    Blocks.emitted (sourceExpressions u D) (F.clauses.length^u) (Complexity.formulaWords F)=
      (rawSourceList F u D).flatMap SourceEncoding.equationWords := by
  rw [Blocks.emitted,←GraphRegisters.finRange_vals,Hastad.SourceEnumeration.rawSourceList_flatMap]
  have hc : (clauseEncoding F u).enumerate=
      (List.finRange (F.clauses.length^u)).map (clauseEncoding F u).code.symm := by
    exact List.ofFn_eq_map
  rw [hc]
  simp only [List.flatMap_map]
  conv_rhs => erw [List.flatMap_map]
  apply congrArg (List.flatMap · (List.finRange (F.clauses.length^u)))
  funext z
  have he := sourceExpressions_eval (D:=D) F ((clauseEncoding F u).code.symm z)
  simp only [Blocks.block,inputTuple,
    Hastad.SourceEnumeration.testTapeEncoding_enumerate,List.flatMap_assoc,List.flatMap_map,
    sourceEquation] at he ⊢
  erw [Equiv.apply_symm_apply] at he
  exact he

def sourceVariableExpr (u : ℕ) : AExpr :=
  .add (.mul ((AExpr.reg 0).pow u) (.const (2^(2^u))))
    (.add (.mul ((AExpr.reg 1).pow u) (.const (2^(8^u)))) (.const 1))
def sourceCountExpr (u D : ℕ) : AExpr :=
  .div (.mul ((AExpr.reg 1).pow u) (.const (sourceExpressions u D).length)) (.const 4)
def sourceStageWords (u D : ℕ) (v : List ℕ) : List ℕ :=
  (sourceVariableExpr u).eval v::(sourceCountExpr u D).eval v::
    (Blocks.emitted (sourceExpressions u D) (((AExpr.reg 1).pow u).eval v) v++
      Blocks.retained (sourceExpressions u D) (((AExpr.reg 1).pow u).eval v) v)
def sourceStageProgram (u D : ℕ) : PolyProgram (sourceStageWords u D) :=
  ((sourceVariableExpr u).program.cons ((sourceCountExpr u D).program.cons
    (Blocks.forward (sourceExpressions u D) ((AExpr.reg 1).pow u)))).ofEq (by intro v; rfl)

lemma sourceVariableExpr_eval (F : Formula) (u : ℕ) :
    (sourceVariableExpr u).eval (Complexity.formulaWords F)=nBits F u := by
  simp only [sourceVariableExpr,AExpr.eval,AExpr.eval_pow,Complexity.formulaWords,List.cons_append,List.nil_append,
    List.drop_zero,List.headI_cons,List.drop_succ_cons,nBits_eq]

lemma sourceCountExpr_eval (F : Formula) (u D : ℕ) :
    (sourceCountExpr u D).eval (Complexity.formulaWords F)=(rawSourceList F u D).length := by
  have h := congrArg List.length (emitted_source F u D)
  rw [Blocks.length_emitted] at h
  have hl : ((rawSourceList F u D).flatMap SourceEncoding.equationWords).length=
      (rawSourceList F u D).length*4 := by
    simp only [List.length_flatMap,SourceEncoding.equationWords,List.length_cons,List.length_nil]
    simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
  rw [hl] at h
  simp only [sourceCountExpr,AExpr.eval,AExpr.eval_pow,Complexity.formulaWords,List.cons_append,List.nil_append,
    List.drop_zero,List.headI_cons,List.drop_succ_cons,h]
  omega

lemma sourceStageWords_spec (F : Formula) (u D : ℕ) (hD : 0<D) (hne : F.clauses≠[]) :
    ∃junk, sourceStageWords u D (Complexity.formulaWords F)=
      SourceEncoding.inputWords (sourceInput F u D hD)++junk := by
  refine ⟨Blocks.retained (sourceExpressions u D) (F.clauses.length^u) (Complexity.formulaWords F),?_⟩
  unfold sourceStageWords
  rw [sourceVariableExpr_eval,sourceCountExpr_eval]
  have ht : ((AExpr.reg 1).pow u).eval (Complexity.formulaWords F)=F.clauses.length^u := by
    simp only [AExpr.eval_pow,AExpr.eval,Complexity.formulaWords,List.cons_append,List.nil_append,
      List.drop_succ_cons,List.drop_zero,List.headI_cons]
  rw [ht,emitted_source]
  simp only [SourceEncoding.inputWords,sourceInput,sourceList_nonempty F u D hne,
    List.cons_append,List.nil_append]
end
end MinUncut.SourceTemplate

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.PCP
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad.SourceContexts
open MinUncut.Costed MinUncut.SourceTemplate UEncoding
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
lemma O.sourceAddress {u : P → ℕ} (hu : Computable u) {s : ∀p,A p → SlotContext (u p)}
    (hs : c.Map (Source.slotContexts.pullback u hu) s)
    {f : ∀p,A p × Signature (u p) → LocalKey (u p)}
    (hf : (c.prod (Source.signatures.pullback u hu)).Map
      (Source.keys.pullback (fun p=>(u p,0)) (hu.pair (Computable.const 0))) f) :
    O c (fun p x=>addressExpr (s p x) (fun S=>f p (x,S))) := by
  have hp := hu.pair (Computable.const 0)
  have tag := O.sourceLookup hu ((Source.out_keyTag.pullback hp).comp hf)
  have tab := O.sourceLookup hu ((Source.out_keyTable.pullback hp).comp hf)
  have reg1 : O c (fun p _=>(AExpr.reg 1).pow (u p)) := (O.fixed (.reg 1)).pow (out_const c hu)
  have reg2 : O c (fun p _=>(AExpr.reg 2).pow (u p)) := (O.fixed (.reg 2)).pow (out_const c hu)
  have b2 := ca_pow (Computable.const 2) (ca_pow (Computable.const 2) hu)
  have b8 := ca_pow (Computable.const 2) (ca_pow (Computable.const 8) hu)
  have left := reg1.mul (O.const (out_const c b2))
  have ha := left.add (reg2.mul (O.const (out_const c b8)))
  have hb := left.add (tab.add ((O.const (out_const c b8)).mul (O.fixed (.reg 0))))
  have hc := tab.add ((O.const (out_const c b2)).mul (O.sourceSampled hu hs))
  exact (tag.eq (O.fixed (.const 0))).cond ((tag.eq (O.fixed (.const 1))).cond ha hb) hc

abbrev sourceArgs := Source.sls.prod Source.tapes
lemma map_sourceContext : (sourceArgs.prod Source.sigs).Map Source.context
    (fun _ x=>((x.2,x.1.1),x.1.2)) :=
  map_pair (map_pair (map_snd _ _) ((map_fst _ _).first)) ((map_snd _ _).first)
lemma out_sourceEquationExpressions : sourceArgs.Out
    (fun _ x=>(equationExpressions x.1 x.2).map (fun e=>e.program.code)) := by
  have hs := map_fst Source.sls Source.tapes
  have he := map_comp map_sourceContext Source.map_localEquation
  have h1 := map_comp he (map_eqFirst Source.keys)
  have h2 := map_comp he (map_eqSecond Source.keys)
  have h3 := map_comp he (map_eqThird Source.keys)
  have hb := (out_boolNat (map_comp he (map_eqRhs Source.keys)))
  have a := O.sourceAddress (c:=sourceArgs) Computable.fst hs h1
  have b := O.sourceAddress (c:=sourceArgs) Computable.fst hs h2
  have d := O.sourceAddress (c:=sourceArgs) Computable.fst hs h3
  have e := O.sourceLookup (c:=sourceArgs) Computable.fst hb
  exact a.cons (b.cons (d.cons (e.cons (out_const sourceArgs (Computable.const [])))))
lemma c_sourceExpressions : Computable (fun p : Source.Par=>
    (sourceExpressions p.1 p.2).map (fun e=>e.program.code)) := by
  have h := (out_list out_sourceEquationExpressions).enumerate
  apply (Primrec.list_flatten.to_comp.comp (Primrec.list_flatten.to_comp.comp h)).of_eq
  intro p
  simp only [sourceExpressions,List.flatMap_def,List.map_flatten,List.flatten_flatten,List.map_map,Function.comp_def]
  rfl

open MinUncut.Costed MinUncut.SourceTemplate MinUncut.CodeEffective
lemma c_sourceVariableExpr : C sourceVariableExpr := by
  exact ((C.fixed (.reg 0)).pow Computable.id |>.mul (C.const
      (ca_pow (Computable.const 2) (ca_pow (Computable.const 2) Computable.id)))).add
    (((C.fixed (.reg 1)).pow Computable.id |>.mul (C.const
      (ca_pow (Computable.const 2) (ca_pow (Computable.const 8) Computable.id)))).add (C.fixed (.const 1)))
lemma c_sourceCountExpr : C (fun p : Source.Par=>sourceCountExpr p.1 p.2) := by
  have hl : Computable (fun p : Source.Par=>(sourceExpressions p.1 p.2).length) :=
    (Computable.list_length.comp c_sourceExpressions).of_eq (fun p=>List.length_map ..)
  exact (((C.fixed (.reg 1)).pow Computable.fst).mul (C.const hl)).div (C.fixed (.const 4))
lemma c_sourceStageCode : Computable (fun p : Source.Par=>(sourceStageProgram p.1 p.2).code) := by
  have hf := p_forwardCode.to_comp.comp c_sourceExpressions ((C.fixed (.reg 1)).pow Computable.fst)
  have hh := computable_cons.comp (c_sourceVariableExpr.precomp Computable.fst)
    (computable_cons.comp c_sourceCountExpr hf)
  apply hh.of_eq
  intro p
  rw [forwardCode_eq]
  rfl
end MinUncut.Preprocess.Syntax

open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
attribute [local instance] Classical.propDecidable

variable {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}

lemma sum_flatMap_nat {A : Type*} (l : List A) (f : A → List ℕ) :
    (l.flatMap f).sum=(l.map (fun a=>(f a).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

lemma tupleList_sum (input : SourceEncoding.Input) (f : (Fin t → Fin input.equations.length) → ℕ) :
    ((tupleList input t).map f).sum=∑u,f u := by
  simp only [tupleList,←List.ofFn_eq_map,List.map_ofFn,List.sum_ofFn]
  exact Equiv.sum_comp finFunctionFinEquiv.symm f

lemma tupleDemands_failure (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ)
    (σ η : ℚ) (y : Fin (paddedVariableEncoding input.«variables» t).size → Bool) :
    listFailure (tupleDemands input u E a b σ η) y=
      ∑e : Index (Fin t) k m n g,repetitions a b e*failure
        (allDemand (equations input) g σ η (occurrence (equations input) (u,e))) (y ∘ variableCode) := by
  unfold tupleDemands listFailure
  simp only [List.map_flatMap,sum_flatMap_nat,List.map_replicate,List.sum_replicate,
    nsmul_eq_mul,Nat.cast_id,failure_map]
  exact E.sum_values _

lemma generatedDemands_failure (input : SourceEncoding.Input)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ)
    (σ η : ℚ) (y : Fin (paddedVariableEncoding input.«variables» t).size → Bool) :
    listFailure (generatedDemands input E a b σ η) y=
      ∑u,∑e : Index (Fin t) k m n g,repetitions a b e*failure
        (allDemand (equations input) g σ η (occurrence (equations input) (u,e))) (y ∘ variableCode) := by
  unfold generatedDemands listFailure
  rw [List.map_flatMap,sum_flatMap_nat]
  change ((tupleList input t).map (fun u=>listFailure (tupleDemands input u E a b σ η) y)).sum=_
  simp only [tupleDemands_failure]
  exact tupleList_sum input _

lemma generated_failure_eq {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input)
    [Nonempty (Fin input.equations.length)]
    (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))
    (y : Fin (paddedVariableEncoding input.«variables» P.o.t).size → Bool) :
    listFailure (generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) y=
      listFailure (P.canonicalDemands (equations input)) y := by
  rw [generatedDemands_failure,Parameters.canonicalDemands,listFailure_map,listFailure_demandList]
  have he := Equiv.sum_comp (occurrence (k:=P.o.k) (m:=P.d.m) (n:=P.d.n)
    (g:=P.grid) (equations input)) (fun e=>multiplicity (P.denominator (Fin input.equations.length))
      (P.weight (equations input) e)*failure (P.demand (equations input) e) (y ∘ variableCode))
  rw [Fintype.sum_prod_type] at he
  rw [←he]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  exact (occurrence_multiplicity (equations input) (by simpa only [Fintype.card_fin] using P.k_le)
    P.grid_pos.1 P.grid_pos.2 (rationalRate_bounds P.hJ P.d P.hd).1
    (rationalRate_bounds P.hJ P.d P.hd).2 _
    (rationalBudgets_pos P.hJ P.d P.hd P.o P.ho) u e).symm
end MinUncut.Costed.SourceWords

end

end OAI
