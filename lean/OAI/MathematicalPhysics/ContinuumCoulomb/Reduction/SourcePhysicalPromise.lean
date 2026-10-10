import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePositiveMargin
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceUnitCoulomb

namespace OAI

/-! Promise transfer for the literal physical thresholds. The retained
source margin absorbs the finite, continuum, and scalar-evaluation errors. -/

noncomputable section
namespace ContinuumCoulomb.SourcePhysicalThreshold

def exactSourceEnergy (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) (v : ℝ) : ℝ :=
  let x := input rho C eps c s p h k A B q d
  CenteredPhysicalThreshold.actualOffset rho x.1 +
    (CenteredPhysicalThreshold.amplification rho x.1.1.1 : ℝ) *
      ((x.2.1 : ℝ)^2 * (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) -
        (x.2.2.2.sum : ℝ)) - v)

theorem exact_endpoint_differences (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) (v : ℝ) :
    let x := input rho C eps c s p h k A B q d
    let a := (SourceNuclearProgram.amplification rho k d : ℝ) *
      (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2
    (AffinePhysicalThreshold.exactValue rho x v).1 - exactSourceEnergy rho C eps c s p h k A B q d v =
      a * ((SourcePositiveProgram.output s d).lower - SourcePositiveProgram.energy (SourcePositiveProgram.output s d)) ∧
    exactSourceEnergy rho C eps c s p h k A B q d v - (AffinePhysicalThreshold.exactValue rho x v).2 =
      a * (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) - (SourcePositiveProgram.output s d).upper) := by
  dsimp only
  simp only [AffinePhysicalThreshold.exactValue,AffinePhysicalThreshold.exactFinite,
    exactSourceEnergy,input,SourceNuclearProgram.amplification,Rat.cast_inv,Rat.cast_natCast]
  constructor <;> ring

end ContinuumCoulomb.SourcePhysicalThreshold

namespace ContinuumCoulomb.SourceUnitCoulomb

theorem promise_transfer (rho C U F K : ℕ) (hrho : 0 < rho) (eps c : ℚ)
    (s p h k A B q ap : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hp : d.PolynomialPromise s) {m : ℕ} (u : Fin m → CoulombPairSum.Point)
    (hu : Function.Injective u)
    (hsites : SourceNuclearProgram.sites rho C eps c s p h k A B d = List.ofFn u)
    (ho : (value rho C U F K eps c s p h k A B q ap d).Valid)
    (center continuumError finiteError : ℝ)
    (hground : ((center-continuumError : ℝ) : EReal) ≤
        unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho) ∧
      unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho) ≤
        ((center+continuumError : ℝ) : EReal))
    (hfinite : |center - SourcePhysicalThreshold.exactSourceEnergy rho C eps c s p h k A B q d
      (CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u)| ≤ finiteError)
    (hbudget : continuumError + finiteError + 1 / (((SourceContactProgram.size d^q : ℕ) : ℝ)+1) ≤
      (SourceNuclearProgram.amplification rho k d : ℝ) *
        (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2 *
        (1 / (2048 * ((SourceMetadataProgram.size d^s : ℕ) : ℝ)))) :
    (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
      unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho) ≤
        (((value rho C U F K eps c s p h k A B q ap d).lower.value : ℝ) : EReal)) ∧
    ((d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
      (((value rho C U F K eps c s p h k A B q ap d).upper.value : ℝ) : EReal) ≤
        unitGroundEnergy ((value rho C U F K eps c s p h k A B q ap d).toData ho)) := by
  let v := CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u
  let x := SourcePhysicalThreshold.input rho C eps c s p h k A B q d
  let a := (SourceNuclearProgram.amplification rho k d : ℝ) *
    (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2
  have ha : 0 ≤ a := by
    apply mul_nonneg _ (sq_nonneg _)
    exact (CenteredPhysicalThreshold.amplification_bound rho _ hrho).1
  have herr := actual_threshold_error rho C U F K hrho eps c s p h k A B q ap d u hu hsites
  have hdiff := SourcePhysicalThreshold.exact_endpoint_differences rho C eps c s p h k A B q d v
  change (AffinePhysicalThreshold.exactValue rho x v).1 -
      SourcePhysicalThreshold.exactSourceEnergy rho C eps c s p h k A B q d v =
      a * ((SourcePositiveProgram.output s d).lower - SourcePositiveProgram.energy (SourcePositiveProgram.output s d)) ∧
    SourcePhysicalThreshold.exactSourceEnergy rho C eps c s p h k A B q d v -
      (AffinePhysicalThreshold.exactValue rho x v).2 =
      a * (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) - (SourcePositiveProgram.output s d).upper) at hdiff
  have hfe := abs_le.mp hfinite
  have hlow := abs_le.mp herr.1
  have hhigh := abs_le.mp herr.2
  constructor
  · intro hy
    have hm := mul_le_mul_of_nonneg_left (SourcePositiveProgram.output_yes_margin s d hd hp hy) ha
    have hl : center+continuumError ≤ (value rho C U F K eps c s p h k A B q ap d).lower.value := by
      dsimp only [a] at hm
      nlinarith only [hm,hdiff.1,hbudget,hfe.2,hlow.1]
    exact hground.2.trans (EReal.coe_le_coe_iff.mpr hl)
  · intro hn
    have hm := mul_le_mul_of_nonneg_left (SourcePositiveProgram.output_no_margin s d hd hp hn) ha
    have hh : ((value rho C U F K eps c s p h k A B q ap d).upper.value : ℝ) ≤ center-continuumError := by
      dsimp only [a] at hm
      nlinarith only [hm,hdiff.2,hbudget,hfe.1,hhigh.2]
    exact (EReal.coe_le_coe_iff.mpr hh).trans hground.1

end ContinuumCoulomb.SourceUnitCoulomb

end

end OAI
