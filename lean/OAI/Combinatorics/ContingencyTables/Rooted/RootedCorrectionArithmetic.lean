import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleDraw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCorrectionArithmetic
import OAI.Combinatorics.ContingencyTables.Transport.PowerOfTwoApproximation

namespace OAI

/-! # Rational evaluation of the literal integer-population correction -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def correctionExponent (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) : ℚ :=
  (gridExponent A R C a z (integerBin A K hK f):ℚ)-
    (a:ℚ)/rationalHeight A C*rationalD A R C z (rationalIntegerPoint A C f)

lemma correctionExponent_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    (correctionExponent A R C a z K hK f:ℝ)=
      (gridExponent A R C a z (integerBin A K hK f):ℝ)-
        (a:ℝ)/height A C*D A R C z (integerPoint A C f) := by
  simp only [correctionExponent,Rat.cast_sub,Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,
    rationalHeight_cast,rationalD_cast,rationalIntegerPoint_cast]

/-- The exponent passed to numerical approximation is a bounded rational,
although the original capacities may be arbitrarily large. -/
theorem correctionExponent_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hB : (K:ℝ)=binWidth A C) (f : FreeIndex A.small A.T A.b) :
    -2 ≤ correctionExponent A R C a z K hK f ∧ correctionExponent A R C a z K hK f ≤ 2 := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  have hd := exponent_change A R C a hCR (Nat.cast_nonneg _) haHR z
    (realCorner (integerBin A K hK f)) (integerPoint A C f) 1 (by norm_num)
    (fun i => by simpa only [abs_sub_comm] using integerPoint_distance A C K hK hB f i)
  have he := gridExponent_eq_floor A R C a z (integerBin A K hK f)
  have hlo := Int.floor_le ((a:ℝ)/height A C*D A R C z (realCorner (integerBin A K hK f)))
  have hhi := Int.lt_floor_add_one ((a:ℝ)/height A C*D A R C z (realCorner (integerBin A K hK f)))
  rw [←he] at hlo hhi
  have hbounds : (-2:ℝ) ≤ (correctionExponent A R C a z K hK f:ℝ) ∧
      (correctionExponent A R C a z K hK f:ℝ) ≤ 2 := by
    rw [correctionExponent_cast]
    simp only [Int.cast_natCast] at hlo hhi
    rcases abs_le.mp hd with ⟨hl,hu⟩
    constructor <;> linarith
  constructor
  · exact_mod_cast hbounds.1
  · exact_mod_cast hbounds.2

lemma correction_eq_population_power (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    correction A R C a z K hK f=(rationalPopulation A K hK f:ℝ)*
      (2:ℝ)^(correctionExponent A R C a z K hK f:ℝ) := by
  have hV : gridWeight A R C a z (integerBin A K hK f)=
      (2:ℝ)^(-(gridExponent A R C a z (integerBin A K hK f):ℝ)) := by
    unfold gridWeight V DenseWeights.binWeight
    rw [←gridExponent_eq_floor]
    simp only [Int.cast_natCast]
  have hr : rho A R C a z (integerPoint A C f)/gridWeight A R C a z (integerBin A K hK f)=
      (2:ℝ)^(correctionExponent A R C a z K hK f:ℝ) := by
    rw [hV,correctionExponent_cast]
    unfold rho DenseWeights.density
    rw [←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  unfold correction
  rw [mul_div_assoc,hr]
  congr 1
  simp only [rationalPopulation,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]

def computedCorrection (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (sigma : ℚ) (f : FreeIndex A.small A.T A.b) : ℚ :=
  rationalPopulation A K hK f*
    PowerOfTwoApproximation.approximate (correctionExponent A R C a z K hK f) sigma

/-- A deterministic pointwise relative-error guarantee for the actual
rational correction returned on every integer assignment. -/
theorem computedCorrection_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hB : (K:ℝ)=binWidth A C)
    (sigma : ℚ) (hsigma : 0 < sigma) (f : FreeIndex A.small A.T A.b) :
    |(computedCorrection A R C a z K hK sigma f:ℝ)-correction A R C a z K hK f| ≤
      (sigma:ℝ)*correction A R C a z K hK f := by
  have hb := correctionExponent_bounds A R C a hC haH z K hK hB f
  have he := PowerOfTwoApproximation.approximate_error _ sigma hb.1 hb.2 hsigma
  have hp : (0:ℝ) ≤ rationalPopulation A K hK f := by
    exact_mod_cast (rationalPopulation_positive A K hK f).le
  rw [correction_eq_population_power]
  simp only [computedCorrection,Rat.cast_mul]
  rw [←mul_sub,abs_mul,abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left he hp).trans_eq (by ring)

/-- Positivity and a uniform range hold on all executions, independently
of the statistical event used by the estimator. -/
theorem computedCorrection_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (sigma : ℚ) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1/2)
    (f : FreeIndex A.small A.T A.b) :
    (1/16:ℝ) ≤ computedCorrection A R C a z K hK sigma f ∧
      (computedCorrection A R C a z K hK sigma f:ℝ) ≤ 8 := by
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  have hb := correction_bounds A R C a (by exact_mod_cast hC) (Nat.cast_nonneg _) haHR z K hK hW hB f
  have he := computedCorrection_error A R C a hC haH z K hK hB sigma hsigma f
  have hsR : (sigma:ℝ) ≤ 1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hsigmaHalf
  have hprod : (sigma:ℝ)*correction A R C a z K hK f ≤ (1/2)*correction A R C a z K hK f :=
    mul_le_mul_of_nonneg_right hsR (by linarith [hb.1])
  rcases abs_le.mp he with ⟨hl,hu⟩
  constructor <;> nlinarith

end

end ContingencyTables.RootedOracleDensity

end OAI
