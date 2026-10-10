import OAI.Combinatorics.ContingencyTables.Counting.CountingPhaseScalarProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingOracleScheduleProgram

namespace OAI

/-! # Executable rational controls for the adaptive counting phases -/

namespace ContingencyTables.CountingPhaseParametersProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open CountingOracleScheduleProgram ScalarScheduleProgram

abbrev Input := List ℕ × Fraction

def scalar (e : Expr) (z : Input) : ℕ := e.eval z.1
def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fun z : Input => z.1) (g := e.eval) first e.realizer
lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition polynomial_first e.polynomial

def scalarFraction (e : Expr) (z : Input) : Fraction := natural (scalar e z)
def scalarFractionRealizer (e : Expr) : Realizer (scalarFraction e) :=
  composition (f := scalar e) (g := natural) (scalarRealizer e) naturalRealizer
lemma polynomial_scalarFraction (e : Expr) : PolynomialTime (scalarFractionRealizer e) :=
  polynomial_composition (polynomial_scalar e) polynomial_natural

def toleranceDenominator : Expr := 800*(CountingPhaseScalarProgram.h+1)
def tolerance (z : Input) : Fraction := TreeFraction.div (z.2,scalarFraction toleranceDenominator z)
def toleranceRealizer : Realizer tolerance :=
  composition (f := fun z : Input => (z.2,scalarFraction toleranceDenominator z))
    (g := TreeFraction.div) (pair second (scalarFractionRealizer toleranceDenominator))
    TreeFraction.divRealizer
lemma polynomial_tolerance : PolynomialTime toleranceRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_scalarFraction toleranceDenominator)) TreeFraction.polynomial_div

lemma tolerance_val (P W H T N R L : ℕ) (e : Fraction) :
    TreeFraction.val (tolerance ([P,W,H,T,N,R,L],e))=
      CountingPhaseSchedule.tolerance H (TreeFraction.val e) := by
  rw [tolerance,TreeFraction.div_val,scalarFraction,natural_val]
  simp [scalar,toleranceDenominator,CountingPhaseScalarProgram.h,Expr.eval,
    CountingPhaseSchedule.tolerance]

def toleranceSquare (z : Input) : Fraction := TreeFraction.mul (tolerance z,tolerance z)
def toleranceSquareRealizer : Realizer toleranceSquare :=
  composition (f := fun z : Input => (tolerance z,tolerance z)) (g := TreeFraction.mul)
    (pair toleranceRealizer toleranceRealizer) TreeFraction.mulRealizer
lemma polynomial_toleranceSquare : PolynomialTime toleranceSquareRealizer :=
  polynomial_composition (polynomial_pair polynomial_tolerance polynomial_tolerance)
    TreeFraction.polynomial_mul

def observationRatio (z : Input) : Fraction :=
  TreeFraction.div (scalarFraction CountingPhaseScalarProgram.observationNumerator z,
    toleranceSquare z)
def observationRatioRealizer : Realizer observationRatio :=
  composition (f := fun z : Input =>
    (scalarFraction CountingPhaseScalarProgram.observationNumerator z,toleranceSquare z))
    (g := TreeFraction.div)
    (pair (scalarFractionRealizer CountingPhaseScalarProgram.observationNumerator)
      toleranceSquareRealizer) TreeFraction.divRealizer
lemma polynomial_observationRatio : PolynomialTime observationRatioRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_scalarFraction CountingPhaseScalarProgram.observationNumerator)
    polynomial_toleranceSquare) TreeFraction.polynomial_div

def observations (z : Input) : ℕ := ceiling (observationRatio z)+1
def observationsRealizer : Realizer observations :=
  composition (f := fun z : Input => ceiling (observationRatio z)) (g := Nat.succ)
    (composition (f := observationRatio) (g := ceiling) observationRatioRealizer ceilingRealizer)
    successor
lemma polynomial_observations : PolynomialTime observationsRealizer :=
  polynomial_composition (polynomial_composition polynomial_observationRatio polynomial_ceiling)
    polynomial_successor

lemma observations_val (P W H T N R L : ℕ) (e : Fraction) :
    observations ([P,W,H,T,N,R,L],e)=
      CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  rw [observations,ceiling_val,observationRatio,TreeFraction.div_val,
    scalarFraction,natural_val,toleranceSquare,TreeFraction.mul_val,tolerance_val]
  change ⌈((CountingPhaseScalarProgram.observationNumerator.eval [P,W,H,T,N,R,L]:ℕ):ℚ)/
    (CountingPhaseSchedule.tolerance H (TreeFraction.val e)*
      CountingPhaseSchedule.tolerance H (TreeFraction.val e))⌉₊+1= _
  rw [CountingPhaseScalarProgram.observationNumerator_value]
  simp only [CountingPhaseSchedule.observations,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_add,Nat.cast_one,pow_two]

def reciprocalTolerance (z : Input) : Fraction := TreeFraction.div ((1,1),tolerance z)
def reciprocalToleranceRealizer : Realizer reciprocalTolerance :=
  composition (f := fun z : Input => ((1,1),tolerance z)) (g := TreeFraction.div)
    (pair (constant (1,1)) toleranceRealizer) TreeFraction.divRealizer
lemma polynomial_reciprocalTolerance : PolynomialTime reciprocalToleranceRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant (1,1)) polynomial_tolerance)
    TreeFraction.polynomial_div

def reciprocalCeiling (z : Input) : ℕ := ceiling (reciprocalTolerance z)
def reciprocalCeilingRealizer : Realizer reciprocalCeiling :=
  composition (f := reciprocalTolerance) (g := ceiling) reciprocalToleranceRealizer ceilingRealizer
lemma polynomial_reciprocalCeiling : PolynomialTime reciprocalCeilingRealizer :=
  polynomial_composition polynomial_reciprocalTolerance polynomial_ceiling

def precision (z : Input) : ℕ := scalar CountingPhaseScalarProgram.precisionBase z+reciprocalCeiling z
def precisionRealizer : Realizer precision :=
  composition (f := fun z : Input => (scalar CountingPhaseScalarProgram.precisionBase z,
    reciprocalCeiling z)) (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (scalarRealizer CountingPhaseScalarProgram.precisionBase) reciprocalCeilingRealizer) add
lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_pair (polynomial_scalar CountingPhaseScalarProgram.precisionBase)
    polynomial_reciprocalCeiling) polynomial_add

lemma precision_val (P W H T N R L : ℕ) (e : Fraction) :
    precision ([P,W,H,T,N,R,L],e)=
      CountingPhaseSchedule.precision H T N R
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  rw [precision,reciprocalCeiling,ceiling_val,reciprocalTolerance,TreeFraction.div_val,tolerance_val]
  simp only [TreeFraction.val,Nat.cast_one,div_one]
  change CountingPhaseScalarProgram.precisionBase.eval [P,W,H,T,N,R,L]+
    ⌈1/CountingPhaseSchedule.tolerance H (TreeFraction.val e)⌉₊= _
  rw [CountingPhaseScalarProgram.precisionBase_value]
  simp only [CountingPhaseSchedule.precision,TreeFraction.val]
  omega

def noise (z : Input) : Fraction := (1,precision z)
def noiseRealizer : Realizer noise := pair (constant 1) precisionRealizer
lemma polynomial_noise : PolynomialTime noiseRealizer :=
  polynomial_pair (polynomial_constant 1) polynomial_precision

lemma noise_val (P W H T N R L : ℕ) (e : Fraction) :
    TreeFraction.val (noise ([P,W,H,T,N,R,L],e))=
      CountingPhaseSchedule.noise H T N R
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  simp only [noise,TreeFraction.val,Nat.cast_one,precision_val,CountingPhaseSchedule.noise]

end ContingencyTables.CountingPhaseParametersProgram

end OAI
