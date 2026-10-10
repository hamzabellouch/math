import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalSchedule
import OAI.Combinatorics.ContingencyTables.Machines.OffsetCountProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleSchedule
import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Fraction := TreeFraction.Fraction

def ceiling (e : Fraction) : ℕ := OffsetCountPrograms.ceilQuotient e
def ceilingRealizer : Realizer ceiling := OffsetCountPrograms.ceilQuotientRealizer
lemma polynomial_ceiling : PolynomialTime ceilingRealizer := OffsetCountPrograms.polynomial_ceilQuotient

lemma ceiling_val (e : Fraction) : ceiling e=⌈TreeFraction.val e⌉₊ := by
  by_cases h : e.2=0
  · simp only [ceiling,OffsetCountPrograms.ceilQuotient,TreeFraction.val,h,Nat.div_zero,
      Nat.cast_zero,div_zero,Nat.ceil_zero]
  · exact OffsetCountPrograms.ceilQuotient_eq e.1 e.2 (Nat.pos_of_ne_zero h)

def natural (n : ℕ) : Fraction := (n,1)
def naturalRealizer : Realizer natural := pair identity (constant 1)
lemma polynomial_natural : PolynomialTime naturalRealizer :=
  polynomial_pair polynomial_identity (polynomial_constant 1)
lemma natural_val (n : ℕ) : TreeFraction.val (natural n)=(n:ℚ) := by
  simp only [natural,TreeFraction.val,Nat.cast_one,div_one]

/-- Phase index, relative tolerance, and failure allowance. -/
abbrev SampleInput := ℕ×(Fraction×Fraction)
def sampleBase (z : SampleInput) : Fraction := natural (65536*(z.1+1))
def sampleBaseRealizer : Realizer sampleBase :=
  composition (f := fun z : SampleInput => 65536*(z.1+1)) (g := natural)
    (composition (f := fun z : SampleInput => (65536,z.1+1))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 65536) (composition first successor)) multiply) naturalRealizer
lemma polynomial_sampleBase : PolynomialTime sampleBaseRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair (polynomial_constant 65536)
    (polynomial_composition polynomial_first polynomial_successor)) polynomial_multiply) polynomial_natural

def sampleDenominator (z : SampleInput) : Fraction :=
  TreeFraction.mul (z.2.2,TreeFraction.mul (z.2.1,z.2.1))
def sampleDenominatorRealizer : Realizer sampleDenominator :=
  composition (f := fun z : SampleInput => (z.2.2,TreeFraction.mul (z.2.1,z.2.1)))
    (g := TreeFraction.mul)
    (pair (composition second second)
      (composition (f := fun z : SampleInput => (z.2.1,z.2.1)) (g := TreeFraction.mul)
        (pair (composition second first) (composition second first)) TreeFraction.mulRealizer))
    TreeFraction.mulRealizer
lemma polynomial_sampleDenominator : PolynomialTime sampleDenominatorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) TreeFraction.polynomial_mul))
    TreeFraction.polynomial_mul

def sampleRatio (z : SampleInput) : Fraction := TreeFraction.div (sampleBase z,sampleDenominator z)
def sampleRatioRealizer : Realizer sampleRatio :=
  composition (f := fun z : SampleInput => (sampleBase z,sampleDenominator z))
    (g := TreeFraction.div) (pair sampleBaseRealizer sampleDenominatorRealizer) TreeFraction.divRealizer
lemma polynomial_sampleRatio : PolynomialTime sampleRatioRealizer :=
  polynomial_composition (polynomial_pair polynomial_sampleBase polynomial_sampleDenominator)
    TreeFraction.polynomial_div

def sampleCount (z : SampleInput) : ℕ := ceiling (sampleRatio z)
def sampleCountRealizer : Realizer sampleCount :=
  composition (f := sampleRatio) (g := ceiling) sampleRatioRealizer ceilingRealizer
lemma polynomial_sampleCount : PolynomialTime sampleCountRealizer :=
  polynomial_composition polynomial_sampleRatio polynomial_ceiling

lemma sampleCount_val (j : ℕ) (delta failure : Fraction) :
    sampleCount (j,(delta,failure))=
      CompanionOracleDensity.sampleCount j (TreeFraction.val delta) (TreeFraction.val failure) := by
  rw [sampleCount,ceiling_val,sampleRatio,TreeFraction.div_val,sampleBase,natural_val,
    sampleDenominator,TreeFraction.mul_val,TreeFraction.mul_val]
  unfold CompanionOracleDensity.sampleCount
  congr 1
  push_cast
  ring

/-- Ambient dimension and requested relative accuracy. -/
abbrev OffsetInput := ℕ×Fraction
def offsetBase (z : OffsetInput) : Fraction := natural (4096*z.1)
def offsetBaseRealizer : Realizer offsetBase :=
  composition (f := fun z : OffsetInput => 4096*z.1) (g := natural)
    (composition (f := fun z : OffsetInput => (4096,z.1)) (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 4096) first) multiply) naturalRealizer
lemma polynomial_offsetBase : PolynomialTime offsetBaseRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 4096) polynomial_first) polynomial_multiply) polynomial_natural

def offsetRatio (z : OffsetInput) : Fraction := TreeFraction.div (offsetBase z,z.2)
def offsetRatioRealizer : Realizer offsetRatio :=
  composition (f := fun z : OffsetInput => (offsetBase z,z.2)) (g := TreeFraction.div)
    (pair offsetBaseRealizer second) TreeFraction.divRealizer
lemma polynomial_offsetRatio : PolynomialTime offsetRatioRealizer :=
  polynomial_composition (polynomial_pair polynomial_offsetBase polynomial_second) TreeFraction.polynomial_div

def offsetAccuracy (z : OffsetInput) : ℕ := ceiling (offsetRatio z)
def offsetAccuracyRealizer : Realizer offsetAccuracy :=
  composition (f := offsetRatio) (g := ceiling) offsetRatioRealizer ceilingRealizer
lemma polynomial_offsetAccuracy : PolynomialTime offsetAccuracyRealizer :=
  polynomial_composition polynomial_offsetRatio polynomial_ceiling

lemma offsetAccuracy_val (d : ℕ) (delta : Fraction) :
    offsetAccuracy (d,delta)=⌈4096*(d:ℚ)/TreeFraction.val delta⌉₊ := by
  rw [offsetAccuracy,ceiling_val,offsetRatio,TreeFraction.div_val,offsetBase,natural_val]
  simp only [Nat.cast_mul,Nat.cast_ofNat]


/-- The natural mixing factor and the natural height-plus-grid allowance,
followed by the rational per-call accuracy. -/
abbrev TimeInput := (ℕ×ℕ)×Fraction

def timeBase (z : TimeInput) : Fraction := natural (z.1.1*z.1.2)
def timeBaseRealizer : Realizer timeBase :=
  composition (f := fun z : TimeInput => z.1.1*z.1.2) (g := natural)
    (composition first multiply) naturalRealizer
lemma polynomial_timeBase : PolynomialTime timeBaseRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_multiply) polynomial_natural

def timeNumerator (z : TimeInput) : Fraction := natural (16*z.1.1)
def timeNumeratorRealizer : Realizer timeNumerator :=
  composition (f := fun z : TimeInput => 16*z.1.1) (g := natural)
    (composition (f := fun z : TimeInput => (16,z.1.1)) (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 16) (composition first first)) multiply) naturalRealizer
lemma polynomial_timeNumerator : PolynomialTime timeNumeratorRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair (polynomial_constant 16)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply) polynomial_natural

def timeExtra (z : TimeInput) : Fraction := TreeFraction.div (timeNumerator z,z.2)
def timeExtraRealizer : Realizer timeExtra :=
  composition (f := fun z : TimeInput => (timeNumerator z,z.2)) (g := TreeFraction.div)
    (pair timeNumeratorRealizer second) TreeFraction.divRealizer
lemma polynomial_timeExtra : PolynomialTime timeExtraRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeNumerator polynomial_second) TreeFraction.polynomial_div

def timeTotal (z : TimeInput) : Fraction := TreeFraction.add (timeBase z,timeExtra z)
def timeTotalRealizer : Realizer timeTotal :=
  composition (f := fun z : TimeInput => (timeBase z,timeExtra z)) (g := TreeFraction.add)
    (pair timeBaseRealizer timeExtraRealizer) TreeFraction.addRealizer
lemma polynomial_timeTotal : PolynomialTime timeTotalRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeBase polynomial_timeExtra) TreeFraction.polynomial_add

def oracleTime (z : TimeInput) : ℕ := ceiling (timeTotal z)
def oracleTimeRealizer : Realizer oracleTime :=
  composition (f := timeTotal) (g := ceiling) timeTotalRealizer ceilingRealizer
lemma polynomial_oracleTime : PolynomialTime oracleTimeRealizer :=
  polynomial_composition polynomial_timeTotal polynomial_ceiling

lemma oracleTime_val (M B : ℕ) (theta : Fraction) :
    oracleTime ((M,B),theta)=⌈(M:ℚ)*((B:ℚ)+16/TreeFraction.val theta)⌉₊ := by
  have he : (timeExtra ((M,B),theta)).2 ≠ 0 := by
    exact (TreeFraction.normalize_den_pos _).ne'
  rw [oracleTime,ceiling_val,timeTotal,TreeFraction.add_val _ _ (by change (1:ℕ) ≠ 0; decide) he,
    timeBase,natural_val,timeExtra,TreeFraction.div_val,timeNumerator,natural_val]
  congr 1
  push_cast
  ring

lemma oracleTime_instance {I J : Type} [Fintype I] [Fintype J]
    (A : CompanionFactorialApplication.Instance I J) (C K : ℕ) (theta : Fraction) :
    oracleTime ((2*(10000*A.d^2*K)^2,
      CompanionOracleDensity.rationalHeight A C+A.d*K+2),theta)=
      CompanionOracleDensity.oracleTime A C K 1 (TreeFraction.val theta) := by
  rw [oracleTime_val,CompanionOracleDensity.oracleTime]
  rw [←CountingTerminalSchedule.natCeil_ratCast]
  congr 1
  simp only [CompanionOracleDensity.mixingConstant,CompanionOracleDensity.rationalHeight,
    CompanionOracleDensity.height,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,
    Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow]
  ring

end ContingencyTables.CountingOracleScheduleProgram

end OAI
