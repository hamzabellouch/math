import OAI.Combinatorics.ContingencyTables.Machines.RoundedPowerProgram

namespace OAI

/-! # The executed power-of-two approximation used by the weight oracle

Both stages are concrete binary programs: compute the rounded signed
power, then bisect using natural cross-products and shared denominators.
The two allowance lists determine the precision parameters.
-/

namespace ContingencyTables.PowerApproximationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := SignedFloorProgram.Input×(List Bool×List Bool)

def prepare (z : Input) : DyadicRootProgram.Input :=
  ((RoundedPowerProgram.output (z.1,z.2.1),z.2.1),z.2.2)
def prepareRealizer : Realizer prepare :=
  pair (pair
    (composition (f := fun z : Input => (z.1,z.2.1)) (g := RoundedPowerProgram.output)
      (pair first (composition second first)) RoundedPowerProgram.outputRealizer)
    (composition second first)) (composition second second)
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first))
      RoundedPowerProgram.polynomial_output)
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second)

def output (z : Input) : TreeFraction.Fraction := DyadicRootProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition prepareRealizer DyadicRootProgram.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare DyadicRootProgram.polynomial_output

theorem output_value (p n d : ℕ) (degree depth : List Bool)
    (hlo: -2≤((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d≤2) :
    TreeFraction.val (output (((p,n),d),(degree,depth)))=
      PowerOfTwoApproximation.approximation (((p:ℚ)-n)/d) degree.length depth.length := by
  unfold output prepare
  rw [DyadicRootProgram.output_value _ (RoundedPowerProgram.output_denominator_pos _),
    RoundedPowerProgram.output_value p n d degree hlo hhi]
  rfl

/-- The encoded output agrees exactly with the rational value used by
the existing finite-word correction laws. -/
theorem output_approximate (p n d : ℕ) (degree depth : List Bool) (sigma : ℚ)
    (hdegree: degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth: depth.length=PowerOfTwoApproximation.depth sigma)
    (hlo: -2≤((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d≤2) :
    TreeFraction.val (output (((p,n),d),(degree,depth)))=
      PowerOfTwoApproximation.approximate (((p:ℚ)-n)/d) sigma := by
  rw [output_value p n d degree depth hlo hhi,hdegree,hdepth]
  rfl

theorem output_error (p n d : ℕ) (degree depth : List Bool) (sigma : ℚ)
    (hdegree: degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth: depth.length=PowerOfTwoApproximation.depth sigma)
    (hlo: -2≤((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d≤2) (hsigma: 0<sigma) :
    |(TreeFraction.val (output (((p,n),d),(degree,depth))):ℝ)-
        (2:ℝ)^((((p:ℚ)-n)/d):ℝ)|≤
      (sigma:ℝ)*(2:ℝ)^((((p:ℚ)-n)/d):ℝ) := by
  rw [output_approximate p n d degree depth sigma hdegree hdepth hlo hhi]
  simpa only [Rat.cast_div,Rat.cast_sub,Rat.cast_natCast] using
    PowerOfTwoApproximation.approximate_error (((p:ℚ)-n)/d) sigma hlo hhi hsigma

end ContingencyTables.PowerApproximationProgram

end OAI
