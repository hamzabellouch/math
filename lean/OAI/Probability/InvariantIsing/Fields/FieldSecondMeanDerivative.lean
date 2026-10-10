import OAI.Probability.InvariantIsing.Fields.FieldSecondCovariance
import OAI.Probability.InvariantIsing.Fields.FieldAffineMoments

namespace OAI

/-! The actual mixed derivative of one scalar Gaussian recursion step.
The formula uses the affine-noise tangent, so it needs no third spatial
derivative of the incoming scalar payoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

def mixedMean (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫ u, F.shiftedMixed a v u p ∂F.toFieldSmoothFamily.affineLaw a v ζ p) + ζ *
    ((∫ u, F.shiftedMean a v u p * F.shiftedTangent a v u p
      ∂F.toFieldSmoothFamily.affineLaw a v ζ p) -
      F.toFieldSmoothFamily.mean a v ζ p *
        (∫ u, F.shiftedTangent a v u p ∂F.toFieldSmoothFamily.affineLaw a v ζ p))

lemma measurable_shiftedMean (a v : ℝ) (p : ℝ × ℝ) :
    Measurable (fun u => F.shiftedMean a v u p) := F.mX.comp (by fun_prop)

lemma measurable_shiftedTangent (a v : ℝ) (p : ℝ × ℝ) :
    Measurable (fun u => F.shiftedTangent a v u p) :=
  (F.mT.comp (by fun_prop)).add ((F.mX.comp (by fun_prop)).mul (by fun_prop))

lemma measurable_shiftedMixed (a v : ℝ) (p : ℝ × ℝ) :
    Measurable (fun u => F.shiftedMixed a v u p) :=
  (F.mTX.comp (by fun_prop)).add ((F.mXX.comp (by fun_prop)).mul (by fun_prop))

lemma mean_hasFDerivAt (hI : IsOpen I) (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt (F.toFieldSmoothFamily.mean a v ζ)
      (pairLinear (F.mixedMean a v ζ p) (F.toFieldSmoothFamily.curvature a v ζ p)) p := by
  let R := |v| / (2 * Real.sqrt m)
  let B := F.KTX + F.KXX * R
  let A := F.KT + F.KX * R
  let α : (ℝ × ℝ) → ℝ → ℝ := fun q u => F.shiftedMean a v u q
  let Dα : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q u =>
    pairLinear (F.shiftedMixed a v u q) (F.XX (q.1, q.2 + Real.sqrt (a + v * q.1) * u))
  let ν := F.toFieldSmoothFamily.affineLaw a v ζ p
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hX := F.kx_nonneg
  have hXX : 0 ≤ F.KXX := (abs_nonneg _).trans (F.bXX (0, 0))
  have hTX : 0 ≤ F.KTX := (abs_nonneg _).trans (F.bTX (p.1, 0) hp)
  have hT : 0 ≤ F.KT := (abs_nonneg _).trans (F.bT (p.1, 0) hp)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc (q : ℝ × ℝ) (hq : q.1 ∈ I) : |fieldAmplitudeSlope a v q.1| ≤ R :=
    abs_div_two_sqrt_le hm (hlo q.1 hq) v
  have hd := F.toFieldSmoothFamily.affine_average_hasFDerivAt hI α Dα a v ζ hm hlo hhi
    hX (show 0 ≤ B + F.KXX by positivity)
    (fun q => F.measurable_shiftedMean a v q)
    (fun q => (measurable_pairLinear (F.measurable_shiftedMixed a v q)
      (F.mXX.comp (by fun_prop))).aestronglyMeasurable)
    (fun q _ u => (F.bX _).trans (le_mul_of_one_le_right hX (by linarith [abs_nonneg u])))
    (fun q hq u => by
      refine (norm_pairLinear_le _ _).trans ?_
      calc
        _ ≤ B * (1 + |u|) + F.KXX := add_le_add (F.shiftedMixed_bound a v u hq hR (hc q hq)) (F.bXX _)
        _ ≤ (B + F.KXX) * (1 + |u|) ^ 2 := by
          have hq1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
          have hq2 := field_mark_one_add_le_sq u
          nlinarith [mul_le_mul_of_nonneg_left hq1 hXX,
            mul_le_mul_of_nonneg_left hq2 hB])
    (fun q hq u => F.shiftedMean_hasFDerivAt a v u hq (hm.trans_le (hlo q.1 hq))) hp
  have hiX : Integrable (fun u => F.shiftedMean a v u p) ν :=
    F.toFieldSmoothFamily.affineLaw_bounded_integrable a v ζ p
      (F.measurable_shiftedMean a v p) F.KX (fun u => F.bX _)
  have hiXX : Integrable (fun u => F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u)) ν :=
    F.toFieldSmoothFamily.affineLaw_bounded_integrable a v ζ p
      (F.mXX.comp (by fun_prop)) F.KXX (fun u => F.bXX _)
  have hiA : Integrable (fun u => F.shiftedTangent a v u p) ν :=
    F.toFieldSmoothFamily.affineLaw_linear_integrable a v ζ p
      (F.measurable_shiftedTangent a v p) hA (fun u => F.shiftedTangent_bound a v u hp hR (hc p hp))
  have hiB : Integrable (fun u => F.shiftedMixed a v u p) ν :=
    F.toFieldSmoothFamily.affineLaw_linear_integrable a v ζ p
      (F.measurable_shiftedMixed a v p) hB (fun u => F.shiftedMixed_bound a v u hp hR (hc p hp))
  have hiXA : Integrable (fun u => F.shiftedMean a v u p * F.shiftedTangent a v u p) ν := by
    apply F.toFieldSmoothFamily.affineLaw_linear_integrable a v ζ p
      ((F.measurable_shiftedMean a v p).mul (F.measurable_shiftedTangent a v p))
      (mul_nonneg hX hA)
    intro u
    change |F.shiftedMean a v u p * F.shiftedTangent a v u p| ≤ (F.KX * A) * (1 + |u|)
    rw [abs_mul]
    calc
      _ ≤ F.KX * (A * (1 + |u|)) := mul_le_mul (F.bX _)
        (F.shiftedTangent_bound a v u hp hR (hc p hp)) (abs_nonneg _) hX
      _ = _ := by ring
  have hiXXprod : Integrable (fun u => F.shiftedMean a v u p * F.shiftedMean a v u p) ν := by
    apply F.toFieldSmoothFamily.affineLaw_bounded_integrable a v ζ p
      ((F.measurable_shiftedMean a v p).mul (F.measurable_shiftedMean a v p)) (F.KX ^ 2)
    intro u
    change |F.shiftedMean a v u p * F.shiftedMean a v u p| ≤ F.KX ^ 2
    rw [abs_mul]
    simpa only [pow_two, shiftedMean] using mul_self_le_mul_self (abs_nonneg _)
      (F.bX (p.1, p.2 + Real.sqrt (a + v * p.1) * u))
  change HasFDerivAt (F.toFieldSmoothFamily.mean a v ζ)
    ((∫ u, Dα p u + (ζ * α p u) • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν) -
      (∫ u, α p u ∂ν) • (∫ u, ζ • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν)) p at hd
  have he := field_pair_covariance ν ζ (α p) (fun u => F.shiftedMixed a v u p)
    (fun u => F.XX (p.1, p.2 + Real.sqrt (a + v * p.1) * u))
    (fun u => F.shiftedTangent a v u p) (fun u => F.shiftedMean a v u p)
    hiB hiXX hiA hiX hiXA hiXXprod
  change ((∫ u, Dα p u + (ζ * α p u) • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν) -
    (∫ u, α p u ∂ν) • (∫ u, ζ • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν)) = _ at he
  rw [he] at hd
  simpa only [mixedMean, FieldSmoothFamily.curvature, FieldSmoothFamily.mean,
    gaussianTiltAverage, FieldSmoothFamily.affineLaw, FieldSmoothFamily.affineShift,
    α, Dα, ν, shiftedMean, pow_two] using hd

end FieldSecondFamily
end InvariantIsing

end

end OAI
