import OAI.Probability.InvariantIsing.Fields.FieldAffineRecursion
import OAI.Probability.InvariantIsing.Fields.FieldTiltedFamilyDerivative

namespace OAI

/-! Second-derivative data for the actual two-coordinate scalar recursion.
The first coordinate is a finite covariance variation; the second is the
scalar field. All bounds are local in the covariance coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

structure FieldSecondFamily (I : Set ℝ) extends FieldSmoothFamily I where
  TX : ℝ × ℝ → ℝ
  TT : ℝ × ℝ → ℝ
  KTX : ℝ
  KTT : ℝ
  mTX : Measurable TX
  mTT : Measurable TT
  bTX : ∀ p, p.1 ∈ I → |TX p| ≤ KTX
  bTT : ∀ p, p.1 ∈ I → |TT p| ≤ KTT
  derivativeX : ∀ p, p.1 ∈ I → HasFDerivAt X (pairLinear (TX p) (XX p)) p
  derivativeT : ∀ p, p.1 ∈ I → HasFDerivAt T (pairLinear (TT p) (TX p)) p

/-- The actual log-cosh terminal has zero covariance derivatives. -/
def fieldLogCoshSecondFamily (I : Set ℝ) : FieldSecondFamily I where
  toFieldSmoothFamily := fieldLogCoshFamily I
  TX := fun _ => 0
  TT := fun _ => 0
  KTX := 0
  KTT := 0
  mTX := measurable_const
  mTT := measurable_const
  bTX := fun _ _ => by simp
  bTT := fun _ _ => by simp
  derivativeX := fun p _ => by
    have h := (field_hasDerivAt_tanh p.2).hasFDerivAt.comp p hasFDerivAt_snd
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm, fieldLogCoshFamily]
  derivativeT := fun p _ => by
    convert hasFDerivAt_const (0 : ℝ) p using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear]

/-- First derivative of the square-root amplitude. -/
def fieldAmplitudeSlope (a v t : ℝ) : ℝ := v / (2 * Real.sqrt (a + v * t))

/-- Its second derivative, written in the chain-rule product form. -/
def fieldAmplitudeCurvature (a v t : ℝ) : ℝ :=
  -(v / 2) * (Real.sqrt (a + v * t) ^ 2)⁻¹ * fieldAmplitudeSlope a v t

lemma fieldAmplitudeSlope_hasDerivAt (a v t : ℝ) (hv : 0 < a + v * t) :
    HasDerivAt (fieldAmplitudeSlope a v) (fieldAmplitudeCurvature a v t) t := by
  have hs : HasDerivAt (fun q => Real.sqrt (a + v * q)) (fieldAmplitudeSlope a v t) t := by
    have hinner : HasDerivAt (fun q : ℝ => a + v * q) v t := by
      convert ((hasDerivAt_id t).const_mul v).const_add a using 1 <;> simp
    convert (Real.hasDerivAt_sqrt hv.ne').comp t hinner using 1
    · rfl
    · dsimp only [fieldAmplitudeSlope]
      ring
  have hi := ((hasDerivAt_inv (Real.sqrt_pos.mpr hv).ne').comp t hs).const_mul (v / 2)
  convert hi using 1
  · funext q
    dsimp only [fieldAmplitudeSlope, Function.comp_def]
    ring
  · dsimp only [fieldAmplitudeCurvature]
    ring

namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

/-- The affine-noise image of the physical spin mean. -/
def shiftedMean (a v u : ℝ) (p : ℝ × ℝ) : ℝ :=
  F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u)

/-- The raw covariance tangent of the affine-noise image of the value. -/
def shiftedTangent (a v u : ℝ) (p : ℝ × ℝ) : ℝ :=
  F.T (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
    F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u) * (fieldAmplitudeSlope a v p.1 * u)

lemma shiftedMean_hasFDerivAt (a v u : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    (hv : 0 < a + v * p.1) :
    HasFDerivAt (F.shiftedMean a v u)
      (pairLinear
        (F.TX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
          F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
            (fieldAmplitudeSlope a v p.1 * u))
        (F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u))) p := by
  exact affine_gaussian_shift_hasFDerivAt F.derivativeX a v u hp hv

lemma shiftedTangent_hasFDerivAt (a v u : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    (hv : 0 < a + v * p.1) :
    HasFDerivAt (F.shiftedTangent a v u)
      (pairLinear
        (F.TT (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
          2 * F.TX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
            (fieldAmplitudeSlope a v p.1 * u) +
          F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
            (fieldAmplitudeSlope a v p.1 * u) ^ 2 +
          F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
            (fieldAmplitudeCurvature a v p.1 * u))
        (F.TX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
          F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
            (fieldAmplitudeSlope a v p.1 * u))) p := by
  have hT := affine_gaussian_shift_hasFDerivAt F.derivativeT a v u hp hv
  have hX := F.shiftedMean_hasFDerivAt a v u hp hv
  have hc : HasFDerivAt (fun q : ℝ × ℝ => fieldAmplitudeSlope a v q.1 * u)
      (pairLinear (fieldAmplitudeCurvature a v p.1 * u) 0) p := by
    have h := ((fieldAmplitudeSlope_hasDerivAt a v p.1 hv).mul_const u).hasFDerivAt.comp p
      hasFDerivAt_fst
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm]
  convert hT.add (hX.mul hc) using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro q
    simp [pairLinear, shiftedMean, fieldAmplitudeSlope]
    ring

end FieldSecondFamily
end InvariantIsing

end

end OAI
