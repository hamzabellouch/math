import OAI.Analysis.KadisonKastler.RecoveryContraction
import OAI.Analysis.KadisonKastler.SquareRootCompression
import OAI.Analysis.KadisonKastler.ScalarRecoveryBounds

namespace OAI

/-! # Combining the tracial estimates for the recovered scalar -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

local instance scalarRecoveryOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance scalarRecoveryStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- Reverse triangle inequality in the form needed to restore a spectral
compression. -/
theorem traceOneNorm_le_sub_add (τ : FaithfulTracialState B) (x y : B) :
    traceOneNorm τ x ≤ traceOneNorm τ (x - y) + traceOneNorm τ y := by
  simpa only [sub_add_cancel] using traceOneNorm_add_le τ (x - y) y

/-- The complement of a commuting spectral projection factors the tail
of the compressed square into the two factors used by Hölder. -/
theorem compression_square_tail_factor (p f e : B)
    (he : IsStarProjection e) (hfe : Commute f e) :
    recoveryCompression p f - p * e * (f * f) * e * p =
      (p * f * (1 - e)) * ((1 - e) * f * p) := by
  have heff : e * (f * f) * e = f * e * f := by
    calc
      e * (f * f) * e = (e * f) * (f * e) := by noncomm_ring
      _ = (f * e) * (e * f) := by rw [hfe.eq]
      _ = f * (e * e) * f := by noncomm_ring
      _ = f * e * f := by rw [he.isIdempotentElem.eq]
  have hec : (1 - e) * (1 - e) = 1 - e := by
    noncomm_ring [he.isIdempotentElem.eq]
  calc
    recoveryCompression p f - p * e * (f * f) * e * p =
        p * (f * f - e * (f * f) * e) * p := by
      unfold recoveryCompression
      noncomm_ring
    _ = p * (f * (1 - e) * f) * p := by rw [heff]; noncomm_ring
    _ = (p * f * (1 - e)) * ((1 - e) * f * p) := by
      calc
        p * (f * (1 - e) * f) * p = p * f * ((1 - e) * (1 - e)) * f * p := by rw [hec]; noncomm_ring
        _ = _ := by noncomm_ring

/-- The two-norm tail estimate supplies the one-norm tail of the
compressed square. -/
theorem compression_square_tail_one_le (τ : FaithfulTracialState B)
    (p f e : B) (he : IsStarProjection e) (hfe : Commute f e) :
    traceOneNorm τ (recoveryCompression p f - p * e * (f * f) * e * p) ≤
      traceTwoNorm τ (p * f * (1 - e)) * traceTwoNorm τ ((1 - e) * f * p) := by
  rw [compression_square_tail_factor p f e he hfe]
  exact traceOneNorm_mul_le τ _ _

/-- All analytic losses in scalar recovery are now explicit: the tail
occurs twice, and the square-root compression contributes its variance
error. The recovered scalar uses the actual continuous contraction. -/
theorem recovery_scalar_lower_from_compression
    (τ : FaithfulTracialState B) {n : ℕ} (hn : 0 < n)
    (p f e : B) (hp : IsStarProjection p) (he : IsStarProjection e)
    {η N tail : ℝ}
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ))
    (hmom : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ η)
    (hf : ‖f * f‖ ≤ N)
    (htail : (n : ℝ) * traceOneNorm τ
      (recoveryCompression p f - p * e * (f * f) * e * p) ≤ tail)
    (hmass : 1 - tail ≤ traceOneNorm τ (e * (f * f) * e))
    (hpolar : (n : ℝ) * traceOneNorm τ (p * e * (f * f) * e * p) =
      traceOneNorm τ (CFC.sqrt ((n : ℂ) • (e * p * e)) * (f * f) *
        CFC.sqrt ((n : ℂ) • (e * p * e)))) :
    9 / 10 - 2 * tail - 2 * N * Real.sqrt ((n : ℝ) - 1) * η * Real.sqrt η ≤
      (τ.toLinearMap ((n : ℂ) • (f * recoveryContraction n p f * f))).re := by
  let A := recoveryCompression p f
  let D := p * e * (f * f) * e * p
  let S := CFC.sqrt ((n : ℂ) • (e * p * e))
  have hr := traceOneNorm_le_sub_add τ (e * (f * f) * e) (S * (f * f) * S)
  have hnneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdiff : traceOneNorm τ (e * (f * f) * e - S * (f * f) * S) =
      traceOneNorm τ (S * (f * f) * S - e * (f * f) * e) := by
    unfold traceOneNorm
    rw [← neg_sub (S * (f * f) * S), CFC.abs_neg]
  rw [hdiff] at hr
  have herror := hmom.sqrt_compression_sandwich_error hn hp he hpτ heτ hf
  have hcomp := traceOneNorm_le_sub_add τ D A
  have hdiff2 : traceOneNorm τ (D - A) = traceOneNorm τ (A - D) := by
    unfold traceOneNorm
    rw [← neg_sub A, CFC.abs_neg]
  rw [hdiff2] at hcomp
  have hscaled := mul_le_mul_of_nonneg_left hcomp hnneg
  have hc := recoveryContraction_trace_lower_bound τ hn p f hp
  change (n : ℝ) * traceOneNorm τ D = traceOneNorm τ (S * (f * f) * S) at hpolar
  change traceOneNorm τ (S * (f * f) * S - e * (f * f) * e) ≤ _ at herror
  change (n : ℝ) * traceOneNorm τ (A - D) ≤ tail at htail
  change (n : ℝ) * traceOneNorm τ A - 1 / 10 ≤ _ at hc
  rw [mul_add] at hscaled
  nlinarith

/-- With the manuscript's explicit choice of the power count, the
constructed contraction recovers a scalar at least one half. -/
theorem recovery_scalar_at_least_half
    (τ : FaithfulTracialState B) {n N : ℕ} (hn : 0 < n)
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N)
    (p f e : B) (hp : IsStarProjection p) (he : IsStarProjection e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = ((100 / (N : ℝ) : ℝ) : ℂ))
    (hmom : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ (100 / N))
    (hf : ‖f * f‖ ≤ N)
    (htail : (n : ℝ) * traceOneNorm τ
      (recoveryCompression p f - p * e * (f * f) * e * p) ≤
        Real.pi / (100 * Real.pi))
    (hmass : 1 - Real.pi / (100 * Real.pi) ≤ traceOneNorm τ (e * (f * f) * e))
    (hpolar : (n : ℝ) * traceOneNorm τ (p * e * (f * f) * e * p) =
      traceOneNorm τ (CFC.sqrt ((n : ℂ) • (e * p * e)) * (f * f) *
        CFC.sqrt ((n : ℂ) • (e * p * e)))) :
    1 / 2 ≤ (τ.toLinearMap ((n : ℂ) • (f * recoveryContraction n p f * f))).re := by
  apply recovered_scalar_lower_bound (Nat.succ_le_iff.mpr hn) hsize
  have hb := recovery_scalar_lower_from_compression τ hn p f e hp he hpτ heτ hmom hf
    htail hmass hpolar
  convert hb using 1
  ring

end

end KadisonKastler

end OAI
