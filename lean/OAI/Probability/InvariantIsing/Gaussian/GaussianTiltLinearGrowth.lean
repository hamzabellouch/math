import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldRecursion

namespace OAI

/-! Linear-growth observables are integrable under finite Gaussian tilts
with linear-growth potentials. This supplies the actual recursive loss
integrals, without extra moment hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma exponentialNormMoments_tilted {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (hμ : ExponentialNormMoments μ)
    (F : E → ℝ) (hF : Measurable F) (hFG : HasLinearGrowth F) (b : ℝ) :
    ExponentialNormMoments (μ.tilted (fun x => b * F x)) := by
  have he := integrable_exp_of_linearGrowth μ hμ hF hFG b
  obtain ⟨C, L, _, _, hbF⟩ := hFG
  intro a
  rw [integrable_tilted_iff he]
  change Integrable (fun x => Real.exp (b * F x) * Real.exp (a * ‖x‖)) μ
  apply ((hμ (|b| * L + a)).const_mul (Real.exp (|b| * C))).mono'
    (((hF.const_mul b).exp).mul ((measurable_norm.const_mul a).exp)).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖Real.exp (b * F x) * Real.exp (a * ‖x‖)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb : b * F x ≤ |b| * (C + L * ‖x‖) := by
    calc
      _ ≤ |b| * |F x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbF x) (abs_nonneg b)
  nlinarith

lemma integrable_linearGrowth_tilted {E : Type*} [SeminormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure E) (hμ : ExponentialNormMoments μ)
    (F G : E → ℝ) (hF : Measurable F) (hFG : HasLinearGrowth F)
    (hG : Measurable G) (hGG : HasLinearGrowth G) (b : ℝ) :
    Integrable G (μ.tilted (fun x => b * F x)) := by
  have he := integrable_exp_of_linearGrowth μ hμ hF hFG b
  rw [integrable_tilted_iff he]
  obtain ⟨C, L, hC, hL, hbF⟩ := hFG
  obtain ⟨D, K, hD, hK, hbG⟩ := hGG
  have henv := (hμ (|b| * L + 1)).const_mul (Real.exp (|b| * C) * (D + K))
  apply henv.mono' (((hF.const_mul b).exp).mul hG).aestronglyMeasurable
  apply ae_of_all
  intro x
  have hexp : Real.exp (b * F x) ≤ Real.exp (|b| * C + (|b| * L) * ‖x‖) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |b| * |F x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |b| * (C + L * ‖x‖) := mul_le_mul_of_nonneg_left (hbF x) (abs_nonneg _)
      _ = _ := by ring
  have hn : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
  have h1 : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg _)
  have hg : |G x| ≤ (D + K) * Real.exp ‖x‖ := by
    have hd := mul_le_mul_of_nonneg_left h1 hD
    have hk := mul_le_mul_of_nonneg_left hn hK
    nlinarith [hbG x]
  change ‖Real.exp (b * F x) * G x‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (|b| * C + (|b| * L) * ‖x‖) * ((D + K) * Real.exp ‖x‖) :=
      mul_le_mul hexp hg (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|b| * C) * (D + K) * Real.exp ((|b| * L + 1) * ‖x‖) := by
      rw [Real.exp_add, show (|b| * L + 1) * ‖x‖ = (|b| * L) * ‖x‖ + ‖x‖ by ring,
        Real.exp_add]
      ring

end InvariantIsing

end

end OAI
