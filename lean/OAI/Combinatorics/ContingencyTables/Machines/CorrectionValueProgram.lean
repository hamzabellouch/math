import OAI.Combinatorics.ContingencyTables.Machines.PowerApproximationProgram

namespace OAI

/-! # Binary composition of the correction value

The input contains the computed grid exponent, phase ratio, point
penalty, population factor and two precision marker lists. Normalized
fraction multiplication supplies a positive denominator for the signed
exponent passed to the executed power approximation.
-/

namespace ContingencyTables.CorrectionValueProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Frame := (ℕ×TreeFraction.Fraction)×TreeFraction.Fraction

def weighted (z : Frame) : TreeFraction.Fraction := TreeFraction.mul (z.1.2,z.2)
def weightedRealizer : Realizer weighted :=
  composition (f := fun z : Frame => (z.1.2,z.2)) (g := TreeFraction.mul)
    (pair (composition first second) second) TreeFraction.mulRealizer
lemma polynomial_weighted : PolynomialTime weightedRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) TreeFraction.polynomial_mul

def exponentInput (z : Frame) : SignedFloorProgram.Input :=
  ((z.1.1*(weighted z).2,(weighted z).1),(weighted z).2)
def exponentInputRealizer : Realizer exponentInput :=
  pair (pair
    (composition (f := fun z : Frame => (z.1.1,(weighted z).2))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (composition first first) (composition weightedRealizer second)) multiply)
    (composition weightedRealizer first)) (composition weightedRealizer second)
lemma polynomial_exponentInput : PolynomialTime exponentInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_weighted polynomial_second)) polynomial_multiply)
    (polynomial_composition polynomial_weighted polynomial_first))
    (polynomial_composition polynomial_weighted polynomial_second)

lemma weighted_denominator_pos (z : Frame) : 0<(weighted z).2 :=
  TreeFraction.normalize_den_pos _

lemma exponentInput_value (z : Frame) :
    ((exponentInput z).1.1-(exponentInput z).1.2:ℚ)/(exponentInput z).2=
      (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2 := by
  have hd : ((weighted z).2:ℚ)≠0 := by exact_mod_cast (weighted_denominator_pos z).ne'
  have hw : TreeFraction.val (weighted z)=TreeFraction.val z.1.2*TreeFraction.val z.2 :=
    TreeFraction.mul_val _ _
  rw [←hw]
  simp only [exponentInput,Nat.cast_mul,TreeFraction.val]
  field_simp [hd]

abbrev Input := (Frame×TreeFraction.Fraction)×(List Bool×List Bool)

def powerInput (z : Input) : PowerApproximationProgram.Input :=
  (exponentInput z.1.1,z.2)
def powerInputRealizer : Realizer powerInput :=
  pair (composition (composition first first) exponentInputRealizer) second
lemma polynomial_powerInput : PolynomialTime powerInputRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_exponentInput)
    polynomial_second

def power (z : Input) : TreeFraction.Fraction := PowerApproximationProgram.output (powerInput z)
def powerRealizer : Realizer power :=
  composition (f := powerInput) (g := PowerApproximationProgram.output)
    powerInputRealizer PowerApproximationProgram.outputRealizer
lemma polynomial_power : PolynomialTime powerRealizer :=
  polynomial_composition polynomial_powerInput PowerApproximationProgram.polynomial_output

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul (z.1.2,power z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (z.1.2,power z)) (g := TreeFraction.mul)
    (pair (composition first second) powerRealizer) TreeFraction.mulRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_power) TreeFraction.polynomial_mul

theorem output_value (z : Frame) (population : TreeFraction.Fraction)
    (degree depth : List Bool)
    (hlo : -2 ≤ (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2)
    (hhi : (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2 ≤ 2) :
    TreeFraction.val (output ((z,population),(degree,depth)))=
      TreeFraction.val population*PowerOfTwoApproximation.approximation
        ((z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2) degree.length depth.length := by
  have hl := hlo
  have hh := hhi
  rw [←exponentInput_value z] at hl hh
  rw [output,TreeFraction.mul_val]
  unfold power powerInput
  rw [PowerApproximationProgram.output_value _ _ _ degree depth hl hh,exponentInput_value]

theorem output_approximate (z : Frame) (population : TreeFraction.Fraction)
    (degree depth : List Bool) (sigma : ℚ)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma)
    (hlo : -2 ≤ (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2)
    (hhi : (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2 ≤ 2) :
    TreeFraction.val (output ((z,population),(degree,depth)))=
      TreeFraction.val population*PowerOfTwoApproximation.approximate
        ((z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2) sigma := by
  rw [output_value z population degree depth hlo hhi,hdegree,hdepth]
  rfl

end ContingencyTables.CorrectionValueProgram

end OAI
