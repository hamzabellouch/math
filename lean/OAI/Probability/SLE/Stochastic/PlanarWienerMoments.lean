import OAI.Probability.SLE.Stochastic.PlanarWienerIncrements

namespace OAI

/-! First-moment control of the actual two-coordinate Wiener increments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

local instance : SecondCountableTopology Driver :=
  ContinuousMapZero.isEmbedding_toContinuousMap.secondCountableTopology

lemma planarWiener_increment_integrable (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0) :
    Integrable (fun b => planarWiener (s+δ) b-planarWiener s b) (W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hL := planarWiener_increment_law W hW s δ
  have hx := (measurePreserving_fst (μ := gaussianReal 0 δ) (ν := gaussianReal 0 δ)).hasLaw.comp hL
  have hy := (measurePreserving_snd (μ := gaussianReal 0 δ) (ν := gaussianReal 0 δ)).hasLaw.comp hL
  exact (hx.hasGaussianLaw.integrable).prodMk hy.hasGaussianLaw.integrable

lemma planarWiener_increment_norm_mean (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0) :
    (∫ b, ‖planarWiener (s+δ) b-planarWiener s b‖ ∂W.prod W) ≤
      2*Real.sqrt δ*standardGaussianAbsMoment 1 := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hL := planarWiener_increment_law W hW s δ
  have hx := (measurePreserving_fst (μ := gaussianReal 0 δ) (ν := gaussianReal 0 δ)).hasLaw.comp hL
  have hy := (measurePreserving_snd (μ := gaussianReal 0 δ) (ν := gaussianReal 0 δ)).hasLaw.comp hL
  have hxi : Integrable (fun b => |(planarWiener (s+δ) b-planarWiener s b).1|) (W.prod W) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs] using hx.hasGaussianLaw.integrable.norm
  have hyi : Integrable (fun b => |(planarWiener (s+δ) b-planarWiener s b).2|) (W.prod W) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs] using hy.hasGaussianLaw.integrable.norm
  calc
    _ ≤ ∫ b, |(planarWiener (s+δ) b-planarWiener s b).1|+
        |(planarWiener (s+δ) b-planarWiener s b).2| ∂W.prod W := by
      apply integral_mono (planarWiener_increment_integrable W hW s δ).norm (hxi.add hyi)
      intro b
      change ‖planarWiener (s+δ) b-planarWiener s b‖ ≤
        |(planarWiener (s+δ) b-planarWiener s b).1|+|(planarWiener (s+δ) b-planarWiener s b).2|
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _))
    _ = _ := by
      rw [integral_add hxi hyi]
      have ex := gaussian_abs_moment hx 1
      have ey := gaussian_abs_moment hy 1
      simp only [pow_one,Function.comp_apply] at ex ey
      rw [ex,ey]
      ring

lemma planarWiener_continuous (b : Driver×Driver) : Continuous (fun t => planarWiener t b) :=
  b.1.continuous.prodMk b.2.continuous

lemma planarWiener_joint_measurable :
    Measurable (fun p : ℝ≥0×(Driver×Driver) => planarWiener p.1 p.2) := by
  exact ((continuous_eval.comp (continuous_snd.fst.prodMk continuous_fst)).prodMk
    (continuous_eval.comp (continuous_snd.snd.prodMk continuous_fst))).measurable

end SLEExactGauge

end

end OAI
