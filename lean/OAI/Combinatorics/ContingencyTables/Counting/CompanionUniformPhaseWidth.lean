import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartSchedule
import OAI.Combinatorics.ContingencyTables.Counting.CountingWordsBound
import OAI.Combinatorics.ContingencyTables.Counting.CountingMarkerBounds

namespace OAI

/-! # A computed common padded width for every adaptive phase

All bounds are fixed arithmetic circuits. No numeric phase count controls
an unbounded preprocessing loop.
-/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

abbrev Input := CompanionPhaseContextProgram.Prepared

def oracleInput (z : Input) : RootedOracleConfigProgram.Input :=
  (((z.1,CountingPhaseParametersProgram.noise z.2),0),[])
def oracleInputRealizer : Realizer oracleInput :=
  pair (pair (pair first (composition (f := Prod.snd) (g := CountingPhaseParametersProgram.noise)
    second CountingPhaseParametersProgram.noiseRealizer)) (constant 0)) (constant [])
lemma polynomial_oracleInput : PolynomialTime oracleInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second CountingPhaseParametersProgram.polynomial_noise))
    (polynomial_constant 0)) (polynomial_constant [])

def rawFields (z : Input) : List ℕ := RootedOracleConfigProgram.fields (oracleInput z)++z.2.1
def rawFieldsRealizer : Realizer rawFields :=
  composition (f := fun z : Input => (RootedOracleConfigProgram.fields (oracleInput z),z.2.1))
    (g := fun p : List ℕ×List ℕ => p.1++p.2)
    (pair (composition (f := oracleInput) (g := RootedOracleConfigProgram.fields)
      oracleInputRealizer RootedOracleConfigProgram.fieldsRealizer) (composition second first)) append
lemma polynomial_rawFields : PolynomialTime rawFieldsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_oracleInput RootedOracleConfigProgram.polynomial_fields)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_append

def precision (z : Input) : ℕ := CountingPhaseParametersProgram.precision z.2
def precisionRealizer : Realizer precision :=
  composition (f := Prod.snd) (g := CountingPhaseParametersProgram.precision)
    second CountingPhaseParametersProgram.precisionRealizer
lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition polynomial_second CountingPhaseParametersProgram.polynomial_precision

def initialPrecision (z : Input) : ℕ :=
  CountingPhaseParametersProgram.scalar CountingPhaseScalarProgram.initialPrecision z.2
def initialPrecisionRealizer : Realizer initialPrecision :=
  composition (f := Prod.snd)
    (g := CountingPhaseParametersProgram.scalar CountingPhaseScalarProgram.initialPrecision)
    second (CountingPhaseParametersProgram.scalarRealizer CountingPhaseScalarProgram.initialPrecision)
lemma polynomial_initialPrecision : PolynomialTime initialPrecisionRealizer :=
  polynomial_composition polynomial_second
    (CountingPhaseParametersProgram.polynomial_scalar CountingPhaseScalarProgram.initialPrecision)

def fields (z : Input) : List ℕ := rawFields z++[precision z,initialPrecision z]
def fieldsRealizer : Realizer fields :=
  composition (f := fun z : Input => (rawFields z,[precision z,initialPrecision z]))
    (g := fun p : List ℕ×List ℕ => p.1++p.2)
    (pair rawFieldsRealizer (composition
      (pair precisionRealizer (composition (pair initialPrecisionRealizer (constant [])) listCons)) listCons)) append
lemma polynomial_fields : PolynomialTime fieldsRealizer :=
  polynomial_composition (polynomial_pair polynomial_rawFields
    (polynomial_composition (polynomial_pair polynomial_precision
      (polynomial_composition (polynomial_pair polynomial_initialPrecision (polynomial_constant []))
        polynomial_listCons)) polynomial_listCons)) polynomial_append

def measure (z : Input) : ℕ := (fields z).sum+1
def measureRealizer : Realizer measure := composition (composition fieldsRealizer listSum) successor
lemma polynomial_measure : PolynomialTime measureRealizer :=
  polynomial_composition (polynomial_composition polynomial_fields polynomial_listSum) polynomial_successor

def x : Expr := .input 0
def innerExpression : Expr := 400*(x+1)*x
def timeExpression : Expr := 2*(10000*x^2*x)^2*(x+x*x+2+4096*innerExpression)
def sampleExpression : Expr := 65536*(x+1)*innerExpression^2
def binExpression : Expr := x*(x+1+4*(4096*x*innerExpression+x))
def estimatorExpression : Expr := x*(sampleExpression*(timeExpression*(9*x)))+
  sampleExpression*(timeExpression*(9*x)+binExpression)
def medianExpression : Expr := 64*(x+1)*estimatorExpression
def initialExpression : Expr := x*(x+1)*(x*(3*x+1)+1+x)
def stepExpression : Expr := 1+(x^2+((medianExpression+medianExpression)+x))
def stageExpression : Expr := x*((x+1)*stepExpression)
def phaseExpression : Expr := initialExpression+x*stageExpression+
  (x*stepExpression+(x+1)*(medianExpression+medianExpression))
def widthExpression : Expr := x*(x*phaseExpression)+409600*(x+1)*x+2*x+1

def width (z : Input) : ℕ := widthExpression.eval [measure z]
def widthRealizer : Realizer width :=
  composition (f := fun z : Input => [measure z]) (g := widthExpression.eval)
    (composition (pair measureRealizer (constant [])) listCons) widthExpression.realizer
theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_measure (polynomial_constant [])) polynomial_listCons)
    widthExpression.polynomial

theorem width_value (z : Input) :
    width z=CountingWordsBound.wordPolynomial.eval (measure z)+
      CountingMarkerBounds.paddingPolynomial.eval (measure z)+2*measure z+1 := by
  simp only [width,widthExpression,phaseExpression,initialExpression,stageExpression,stepExpression,
    medianExpression,estimatorExpression,sampleExpression,timeExpression,binExpression,innerExpression,x,
    Expr.eval_power,Expr.eval,CountingWordsBound.wordPolynomial,CountingWordsBound.phasePolynomial,
    CountingWordsBound.initialPolynomial,CountingWordsBound.stagePolynomial,CountingWordsBound.stepPolynomial,
    CountingOracleWordBounds.medianPolynomial,CountingOracleWordBounds.estimatorPolynomial,
    CountingOracleWordBounds.samplePolynomial,CountingOracleWordBounds.timePolynomial,
    CountingOracleWordBounds.binPolynomial,CountingOracleWordBounds.innerPolynomial,
    CountingMarkerBounds.paddingPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,List.getD_cons_zero]

theorem width_pos (z : Input) : 0 < width z := by rw [width_value]; omega

end ContingencyTables.CompanionUniformPhaseWidth

end OAI
