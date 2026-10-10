import OAI.Probability.InvariantIsing.Magnetic.MagneticRelativeThird

namespace OAI

/-! The actual fourth-derivative recursion in centered-cumulant form. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldFourthTransform_centered (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (bM : ∀ x, |M x| ≤ 1) {C D : ℝ}
    (bQ : ∀ x, |Q x| ≤ C) (bR : ∀ x, |R x| ≤ D) (z : ℝ) :
    fieldFourthTransform ζ v F M Q R S z =
      fieldSpinTransition ζ v F S z +
      4 * ζ * (fieldSpinTransition ζ v F (fun x => R x * M x) z -
        fieldSpinTransition ζ v F R z * fieldSpinTransition ζ v F M z) +
      3 * ζ * (fieldSpinTransition ζ v F (fun x => (Q x) ^ 2) z -
        (fieldSpinTransition ζ v F Q z) ^ 2) +
      6 * ζ ^ 2 * (fieldSpinTransition ζ v F
          (fun x => Q x * (M x - fieldSpinTransition ζ v F M z) ^ 2) z -
        fieldSpinTransition ζ v F Q z * fieldSpinTransition ζ v F
          (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 2) z) +
      ζ ^ 3 * (fieldSpinTransition ζ v F
          (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 4) z -
        3 * (fieldSpinTransition ζ v F
          (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 2) z) ^ 2) := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  let T := fun a : ℝ → ℝ => fieldSpinTransition ζ v F a z
  have bRM : ∀ x, |R x * M x| ≤ D := by
    intro x
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (bM x) (abs_nonneg _)).trans (by simpa using bR x)
  have bQ2 : ∀ x, |(Q x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bQ x) 2
  have hRMQ : T (fun x => R x * M x + Q x * Q x) =
      T (fun x => R x * M x) + T (fun x => (Q x) ^ 2) := by
    change fieldSpinTransition ζ v F (fun x => R x * M x + Q x * Q x) z = _
    simp only [← pow_two]
    exact fieldSpinTransition_add ζ v hF hG (hR.mul hM) (hQ.pow_const 2) bRM bQ2 z
  have h2QR : T (fun x => 2 * Q x * Q x + 2 * M x * R x) =
      2 * T (fun x => (Q x) ^ 2) + 2 * T (fun x => R x * M x) := by
    have he : (fun x => 2 * Q x * Q x + 2 * M x * R x) =
        fun x => 2 * ((Q x) ^ 2 + R x * M x) := by funext x; ring
    rw [he]
    change fieldSpinTransition ζ v F (fun x => 2 * ((Q x) ^ 2 + R x * M x)) z = _
    rw [fieldSpinTransition_const_mul]
    have hadd := fieldSpinTransition_add ζ v hF hG (hQ.pow_const 2) (hR.mul hM) bQ2 bRM z
    change fieldSpinTransition ζ v F (fun x => (Q x) ^ 2 + R x * M x) z =
      fieldSpinTransition ζ v F (fun x => (Q x) ^ 2) z +
        fieldSpinTransition ζ v F (fun x => R x * M x) z at hadd
    rw [hadd]
    dsimp only [T]
    ring
  have h2MQ : T (fun x => 2 * M x * Q x) = 2 * T (fun x => Q x * M x) := by
    change (∫ x, 2 * M x * Q x ∂μ) = 2 * ∫ x, Q x * M x ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have h3M2Q : T (fun x => 3 * (M x) ^ 2 * Q x) = 3 * T (fun x => Q x * (M x) ^ 2) := by
    change (∫ x, 3 * (M x) ^ 2 * Q x ∂μ) = 3 * ∫ x, Q x * (M x) ^ 2 ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have h2MQM : T (fun x => (2 * M x * Q x) * M x) = 2 * T (fun x => Q x * (M x) ^ 2) := by
    change (∫ x, (2 * M x * Q x) * M x ∂μ) = 2 * ∫ x, Q x * (M x) ^ 2 ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hQMM : T (fun x => (Q x * M x) * M x) = T (fun x => Q x * (M x) ^ 2) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hM3 : T (fun x => (M x) ^ 2 * M x) = T (fun x => (M x) ^ 3) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hM4 : T (fun x => ((M x) ^ 2 * M x) * M x) = T (fun x => (M x) ^ 4) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hc2 := magnetic_centered_second μ hM bM
  have hc4 := magnetic_centered_fourth μ hM bM
  have hqc2 := magnetic_weighted_centered_second μ hM hQ bM bQ
  change T (fun x => (M x - T M) ^ 2) = T (fun x => (M x) ^ 2) - (T M) ^ 2 at hc2
  change T (fun x => (M x - T M) ^ 4) = T (fun x => (M x) ^ 4) -
    4 * T M * T (fun x => (M x) ^ 3) + 6 * (T M) ^ 2 * T (fun x => (M x) ^ 2) -
    3 * (T M) ^ 4 at hc4
  change T (fun x => Q x * (M x - T M) ^ 2) = T (fun x => Q x * (M x) ^ 2) -
    2 * T M * T (fun x => Q x * M x) + (T M) ^ 2 * T Q at hqc2
  change _ = T S + 4 * ζ * (T (fun x => R x * M x) - T R * T M) +
    3 * ζ * (T (fun x => (Q x) ^ 2) - (T Q) ^ 2) +
    6 * ζ ^ 2 * (T (fun x => Q x * (M x - T M) ^ 2) -
      T Q * T (fun x => (M x - T M) ^ 2)) +
    ζ ^ 3 * (T (fun x => (M x - T M) ^ 4) -
      3 * (T (fun x => (M x - T M) ^ 2)) ^ 2)
  rw [hc2, hc4, hqc2]
  unfold fieldFourthTransform fieldTiltSpatial fieldCurvatureTransform fieldThirdTransform
  change T S + ζ * (T (fun x => R x * M x) - T R * T M) +
    ζ * ((T (fun x => R x * M x + Q x * Q x) +
      ζ * (T (fun x => (Q x * M x) * M x) - T (fun x => Q x * M x) * T M)) -
      ((T R + ζ * (T (fun x => Q x * M x) - T Q * T M)) * T M +
        T Q * (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)))) +
    ζ * ((T (fun x => 2 * Q x * Q x + 2 * M x * R x) +
      ζ * (T (fun x => (2 * M x * Q x) * M x) - T (fun x => 2 * M x * Q x) * T M) +
      ζ * ((T (fun x => 3 * (M x) ^ 2 * Q x) +
        ζ * (T (fun x => ((M x) ^ 2 * M x) * M x) - T (fun x => (M x) ^ 2 * M x) * T M)) -
        ((T (fun x => 2 * M x * Q x) +
          ζ * (T (fun x => (M x) ^ 2 * M x) - T (fun x => (M x) ^ 2) * T M)) * T M +
          T (fun x => (M x) ^ 2) * (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2))))) -
      2 * ((T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)) *
        (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)) +
        T M * ((T R + ζ * (T (fun x => Q x * M x) - T Q * T M)) +
          ζ * ((T (fun x => 2 * M x * Q x) +
            ζ * (T (fun x => (M x) ^ 2 * M x) - T (fun x => (M x) ^ 2) * T M)) -
            2 * T M * (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)))))) = _
  rw [hRMQ, h2QR, h2MQ, h3M2Q, h2MQM, hQMM, hM4, hM3]
  ring

end InvariantIsing

end

end OAI
