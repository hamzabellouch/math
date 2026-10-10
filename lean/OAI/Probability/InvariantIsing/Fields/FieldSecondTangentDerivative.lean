import OAI.Probability.InvariantIsing.Fields.FieldSecondMeanDerivative
import OAI.Probability.InvariantIsing.Fields.FieldRawTangent

namespace OAI

/-! The second covariance derivative of the actual scalar Gaussian
value, obtained by differentiating its raw affine-noise tangent. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing
namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

def secondMean (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫ u, F.shiftedSecond a v u p ∂F.toFieldSmoothFamily.affineLaw a v ζ p) + ζ *
    ((∫ u, (F.shiftedTangent a v u p) ^ 2 ∂F.toFieldSmoothFamily.affineLaw a v ζ p) -
      (∫ u, F.shiftedTangent a v u p ∂F.toFieldSmoothFamily.affineLaw a v ζ p) ^ 2)

lemma measurable_shiftedSecond (a v : ℝ) (p : ℝ × ℝ) :
    Measurable (fun u => F.shiftedSecond a v u p) := by
  exact (((F.mTT.comp (by fun_prop)).add
    (((F.mTX.comp (by fun_prop)).const_mul 2).mul (by fun_prop))).add
    ((F.mXX.comp (by fun_prop)).mul (by fun_prop))).add
    ((F.mX.comp (by fun_prop)).mul (by fun_prop))

lemma tangent_hasFDerivAt (hI : IsOpen I) (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt (F.toFieldSmoothFamily.tangent a v ζ)
      (pairLinear (F.secondMean a v ζ p) (F.mixedMean a v ζ p)) p := by
  let R := |v| / (2 * Real.sqrt m)
  let D := (|v| / 2) * m⁻¹ * R
  let A := F.KT + F.KX * R
  let B := F.KTX + F.KXX * R
  let C := F.KTT + 2 * F.KTX * R + F.KXX * R ^ 2 + F.KX * D
  let α : (ℝ × ℝ) → ℝ → ℝ := fun q u => F.shiftedTangent a v u q
  let Dα : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q u =>
    pairLinear (F.shiftedSecond a v u q) (F.shiftedMixed a v u q)
  let ν := F.toFieldSmoothFamily.affineLaw a v ζ p
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hX := F.kx_nonneg
  have hXX : 0 ≤ F.KXX := (abs_nonneg _).trans (F.bXX (0, 0))
  have hTX : 0 ≤ F.KTX := (abs_nonneg _).trans (F.bTX (p.1, 0) hp)
  have hTT : 0 ≤ F.KTT := (abs_nonneg _).trans (F.bTT (p.1, 0) hp)
  have hT : 0 ≤ F.KT := (abs_nonneg _).trans (F.bT (p.1, 0) hp)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hc (q : ℝ × ℝ) (hq : q.1 ∈ I) : |fieldAmplitudeSlope a v q.1| ≤ R :=
    abs_div_two_sqrt_le hm (hlo q.1 hq) v
  have hd2 (q : ℝ × ℝ) (hq : q.1 ∈ I) : |fieldAmplitudeCurvature a v q.1| ≤ D :=
    fieldAmplitudeCurvature_abs_le a v q.1 hm (hlo q.1 hq)
  have hd := F.toFieldSmoothFamily.affine_average_hasFDerivAt hI α Dα a v ζ hm hlo hhi
    hA (show 0 ≤ C + B by positivity)
    (fun q => F.measurable_shiftedTangent a v q)
    (fun q => (measurable_pairLinear (F.measurable_shiftedSecond a v q)
      (F.measurable_shiftedMixed a v q)).aestronglyMeasurable)
    (fun q hq u => F.shiftedTangent_bound a v u hq hR (hc q hq))
    (fun q hq u => by
      refine (norm_pairLinear_le _ _).trans ?_
      calc
        _ ≤ C * (1 + |u|) ^ 2 + B * (1 + |u|) := add_le_add
          (F.shiftedSecond_bound a v u hq hR hD (hc q hq) (hd2 q hq))
          (F.shiftedMixed_bound a v u hq hR (hc q hq))
        _ ≤ (C + B) * (1 + |u|) ^ 2 := by
          have hh := mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hB
          nlinarith)
    (fun q hq u => F.shiftedTangent_hasFDerivAt a v u hq (hm.trans_le (hlo q.1 hq))) hp
  have hq := (F.toFieldSmoothFamily.affineLaw_quadratic_moment a v ζ p).1
  have hiX : Integrable (fun u => F.shiftedMean a v u p) ν :=
    F.toFieldSmoothFamily.affineLaw_bounded_integrable a v ζ p
      (F.measurable_shiftedMean a v p) F.KX (fun u => F.bX _)
  have hiA : Integrable (fun u => F.shiftedTangent a v u p) ν :=
    F.toFieldSmoothFamily.affineLaw_linear_integrable a v ζ p
      (F.measurable_shiftedTangent a v p) hA (fun u => F.shiftedTangent_bound a v u hp hR (hc p hp))
  have hiB : Integrable (fun u => F.shiftedMixed a v u p) ν :=
    F.toFieldSmoothFamily.affineLaw_linear_integrable a v ζ p
      (F.measurable_shiftedMixed a v p) hB (fun u => F.shiftedMixed_bound a v u hp hR (hc p hp))
  have hiC : Integrable (fun u => F.shiftedSecond a v u p) ν :=
    field_integrable_of_quadratic_bound ν hq (F.measurable_shiftedSecond a v p) C
      (fun u => F.shiftedSecond_bound a v u hp hR hD (hc p hp) (hd2 p hp))
  have hiAA : Integrable (fun u => F.shiftedTangent a v u p * F.shiftedTangent a v u p) ν := by
    apply field_integrable_of_quadratic_bound ν hq
      ((F.measurable_shiftedTangent a v p).mul (F.measurable_shiftedTangent a v p)) (A ^ 2)
    intro u
    change |F.shiftedTangent a v u p * F.shiftedTangent a v u p| ≤ A ^ 2 * (1 + |u|) ^ 2
    rw [abs_mul]
    have hh := mul_self_le_mul_self (abs_nonneg _) (F.shiftedTangent_bound a v u hp hR (hc p hp))
    nlinarith
  have hiAX : Integrable (fun u => F.shiftedTangent a v u p * F.shiftedMean a v u p) ν := by
    apply F.toFieldSmoothFamily.affineLaw_linear_integrable a v ζ p
      ((F.measurable_shiftedTangent a v p).mul (F.measurable_shiftedMean a v p))
      (mul_nonneg hA hX)
    intro u
    change |F.shiftedTangent a v u p * F.shiftedMean a v u p| ≤ (A * F.KX) * (1 + |u|)
    rw [abs_mul]
    calc
      _ ≤ (A * (1 + |u|)) * F.KX := mul_le_mul
        (F.shiftedTangent_bound a v u hp hR (hc p hp)) (F.bX _) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  change HasFDerivAt (fun q => ∫ u, F.shiftedTangent a v u q
    ∂F.toFieldSmoothFamily.affineLaw a v ζ q)
    ((∫ u, Dα p u + (ζ * α p u) • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν) -
      (∫ u, α p u ∂ν) • (∫ u, ζ • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν)) p at hd
  have he := field_pair_covariance ν ζ (α p) (fun u => F.shiftedSecond a v u p)
    (fun u => F.shiftedMixed a v u p) (fun u => F.shiftedTangent a v u p)
    (fun u => F.shiftedMean a v u p) hiC hiB hiA hiX hiAA hiAX
  change ((∫ u, Dα p u + (ζ * α p u) • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν) -
    (∫ u, α p u ∂ν) • (∫ u, ζ • F.toFieldSmoothFamily.affineDifferential a v p u ∂ν)) = _ at he
  rw [he] at hd
  have hcov : (∫ u, F.shiftedTangent a v u p * F.shiftedMean a v u p ∂ν) =
      ∫ u, F.shiftedMean a v u p * F.shiftedTangent a v u p ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ fun u => mul_comm _ _
  have hf : F.toFieldSmoothFamily.tangent a v ζ =ᶠ[𝓝 p]
      (fun q => ∫ u, F.shiftedTangent a v u q ∂F.toFieldSmoothFamily.affineLaw a v ζ q) := by
    filter_upwards [(hI.preimage continuous_fst).mem_nhds hp] with q hqI
    exact (F.rawTangent_eq a v ζ hqI (hm.trans_le (hlo q.1 hqI))).symm
  have hout := hd.congr_of_eventuallyEq hf
  rw [hcov] at hout
  convert hout using 1
  apply ContinuousLinearMap.ext
  intro w
  simp only [secondMean, mixedMean, FieldSmoothFamily.mean, gaussianTiltAverage,
    FieldSmoothFamily.affineLaw, FieldSmoothFamily.affineShift, α, ν,
    shiftedMean, pairLinear_apply, pow_two]
  ring

end FieldSecondFamily
end InvariantIsing

end

end OAI
