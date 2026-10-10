import Mathlib
import OAI.Computability.MinUncut.Estimates.OutputSize
import OAI.Computability.MinUncut.Graphs.DemandOrder
import OAI.Computability.MinUncut.Machines.AlphabetSize

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.Parameters
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness Polynomial
attribute [local instance] Classical.propDecidable

def denominatorCoefficient {J : ℕ} (P : Parameters J) : ℕ :=
  Fintype.card (FixedSets (Fin P.o.t) P.o.k)*3^P.o.t*
    innerDenominator P.o.t P.d.m P.d.n P.grid (rationalRate J P.d) (rationalBudgets J P.d P.o)

def denominatorPolynomial {J : ℕ} (P : Parameters J) : Polynomial ℕ :=
  C P.denominatorCoefficient*X^P.o.t

def variablePolynomial {J : ℕ} (P : Parameters J) : Polynomial ℕ :=
  alphabetSizePolynomial P.o.t

def vertexPolynomial {J : ℕ} (P : Parameters J) : Polynomial ℕ :=
  P.variablePolynomial+C 3*P.denominatorPolynomial*C ⌈rationalWeight J P.d P.o⌉₊

def sizePolynomial {J : ℕ} (P : Parameters J) : Polynomial ℕ :=
  C 3*P.vertexPolynomial+P.vertexPolynomial^2+C 10*P.denominatorPolynomial+C 2

variable {Name S : Type*} [Fintype Name] [Fintype S] [Nonempty S]

omit [Fintype Name] [Nonempty S] in
lemma denominator_eq {J : ℕ} (P : Parameters J) :
    P.denominator S=P.denominatorCoefficient*Fintype.card S^P.o.t := by
  rw [denominator,samplerDenominator_polynomial]
  simp only [Fintype.card_fin,denominatorCoefficient]

omit [Fintype Name] [Nonempty S] in
lemma denominator_le {J L : ℕ} (P : Parameters J) (hS : Fintype.card S≤L) :
    P.denominator S≤P.denominatorPolynomial.eval L := by
  rw [P.denominator_eq]
  simpa only [denominatorPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_X] using Nat.mul_le_mul_left P.denominatorCoefficient (Nat.pow_le_pow_left hS P.o.t)

omit [Fintype S] [Nonempty S] in
lemma variables_le {J L : ℕ} (P : Parameters J) (hN : Fintype.card Name≤L) :
    Fintype.card (FamilyVariable Name (Fin P.o.t))≤P.variablePolynomial.eval L := by
  exact alphabetSizePolynomial_bound (Name := Name) P.o.t L hN

omit [Fintype Name] in
lemma demands_le {J : ℕ} (P : Parameters J) (equations : S → Equation Name) :
    Fintype.card (UnitDemand (P.denominator S) (P.weight equations))≤
      P.denominator S*⌈rationalWeight J P.d P.o⌉₊ := by
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (rationalWeight J P.d P.o))
    (Nat.cast_nonneg (α := ℚ) (P.denominator S))
  rw [← P.graph_demands equations] at hh
  exact_mod_cast hh

lemma vertex_bound {J L : ℕ} (P : Parameters J) (equations : S → Equation Name)
    (hN : Fintype.card Name≤L) (hS : Fintype.card S≤L) :
    (P.graph equations).vertices≤P.vertexPolynomial.eval L := by
  rw [P.graph_vertices,vertexPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_C]
  have he := (P.demands_le equations).trans
    (Nat.mul_le_mul_right _ (P.denominator_le hS))
  exact add_le_add (P.variables_le hN) (by simpa only [mul_assoc] using Nat.mul_le_mul_left 3 he)

lemma size_bound {J L : ℕ} (P : Parameters J) (equations : S → Equation Name)
    (hN : Fintype.card Name≤L) (hS : Fintype.card S≤L) :
    (P.graph equations).vertices+(P.graph equations).bits.length≤P.sizePolynomial.eval L := by
  have hv := P.vertex_bound equations hN hS
  have hd := P.denominator_le hS
  have hb := (P.graph equations).bits_length_le
  rw [P.graph_threshold] at hb
  have hv2 := Nat.pow_le_pow_left hv 2
  simp only [sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C]
  nlinarith
end MinUncut.Outer.Parameters

end
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
noncomputable section

def tupleCountExpr (t : ℕ) : AExpr := (AExpr.reg 1).pow t

def variableCountExpr (t : ℕ) : AExpr :=
  .mul (.add ((AExpr.mul ((AExpr.reg 0).pow 3) (.const 2)).pow t)
      ((AExpr.add (.reg 0) (.mul ((AExpr.reg 0).pow 3) (.const 2))).pow t))
    (.const (2^((2^3)^t)))

def unitCountExpr (es : List AExpr) (t : ℕ) : AExpr :=
  .div (.mul (tupleCountExpr t) (.const es.length)) (.const 3)

def thresholdExpr (t D : ℕ) : AExpr :=
  .mul (.const (5*D)) (tupleCountExpr t)

def demandStageWords (es : List AExpr) (t D : ℕ) (v : List ℕ) : List ℕ :=
  (variableCountExpr t).eval v::(unitCountExpr es t).eval v::(thresholdExpr t D).eval v::
    (Blocks.emitted es ((tupleCountExpr t).eval v) v++Blocks.retained es ((tupleCountExpr t).eval v) v)

def demandStageProgram (es : List AExpr) (t D : ℕ) : PolyProgram (demandStageWords es t D) :=
  ((variableCountExpr t).program.cons ((unitCountExpr es t).program.cons
    ((thresholdExpr t D).program.cons (Blocks.forward es (tupleCountExpr t))))).ofEq (by
      intro v; rfl)

lemma input_regs (input : SourceEncoding.Input) (rest : List ℕ) :
    (SourceEncoding.inputWords input++rest).headI=input.«variables» ∧
    ((SourceEncoding.inputWords input++rest).drop 1).headI=input.equations.length := by
  constructor <;> rfl

lemma tupleCountExpr_eval (input : SourceEncoding.Input) (rest : List ℕ) (t : ℕ) :
    (tupleCountExpr t).eval (SourceEncoding.inputWords input++rest)=input.equations.length^t := by
  simp only [tupleCountExpr,AExpr.eval_pow,AExpr.eval,(input_regs input rest).2]

lemma variableCountExpr_eval (input : SourceEncoding.Input) (rest : List ℕ) (t : ℕ) :
    (variableCountExpr t).eval (SourceEncoding.inputWords input++rest)=
      (paddedVariableEncoding input.«variables» t).size := by
  simp only [variableCountExpr,AExpr.eval,AExpr.eval_pow,List.drop_zero,(input_regs input rest).1,
      paddedVariableEncoding_size]

lemma unitCountExpr_eval {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}
    (input : SourceEncoding.Input) (rest : List ℕ)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) :
    (unitCountExpr (localExpressions E a b σ η) t).eval (SourceEncoding.inputWords input++rest)=
      (generatedDemands input E a b σ η).length := by
  have h := congrArg List.length (emitted_demands input E a b σ η rest)
  rw [Blocks.length_emitted,GraphRegisters.length_packDemands] at h
  simp only [unitCountExpr,AExpr.eval,tupleCountExpr_eval,h]
  omega

lemma thresholdExpr_eval {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input) (rest : List ℕ) :
    (thresholdExpr P.o.t P.denominatorCoefficient).eval (SourceEncoding.inputWords input++rest)=
      5*P.denominator (Fin input.equations.length) := by
  simp only [thresholdExpr,AExpr.eval,tupleCountExpr_eval,P.denominator_eq,Fintype.card_fin,mul_assoc]

lemma demandStageWords_spec {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input)
    (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid)) (rest : List ℕ) :
    ∃junk, demandStageWords (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) P.o.t P.denominatorCoefficient
      (SourceEncoding.inputWords input++rest)=
       (paddedVariableEncoding input.«variables» P.o.t).size::
       (generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
         (rationalSigma J) (rationalEta J)).length::(5*P.denominator (Fin input.equations.length))::
       (GraphRegisters.packDemands (generatedDemands input E (rationalRate J P.d)
         (rationalBudgets J P.d P.o) (rationalSigma J) (rationalEta J))++junk) := by
  refine ⟨Blocks.retained (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
    (rationalSigma J) (rationalEta J)) (input.equations.length^P.o.t)
    (SourceEncoding.inputWords input++rest),?_⟩
  simp only [demandStageWords,variableCountExpr_eval,unitCountExpr_eval,thresholdExpr_eval,
    tupleCountExpr_eval,emitted_demands]

end
end MinUncut.Costed.SourceWords

end OAI
