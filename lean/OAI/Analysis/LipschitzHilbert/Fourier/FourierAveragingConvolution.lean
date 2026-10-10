import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingMeasure
import OAI.Analysis.LipschitzHilbert.Trees.FixedPathAverage
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Sub

namespace OAI

/-!
# Convolution and the exact averaging mixture

Convolution preserves the proved Fourier gap. A central mass of the kernel
minorizes the uniform law on a smaller interval. The remaining measure is
normalized into the probability used in the prediction-mixture argument.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace LipschitzHilbert

open PhaseCombinatorics

theorem fourierMoment_eq_charFun (μ : Measure ℝ) (s : ℝ) :
    fourierMoment μ s = charFun μ s := by
  unfold fourierMoment
  rw [charFun_apply_real]
  simp only [character, Complex.ofReal_mul]

theorem fourierGap_conv_left (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {gap : ℝ} (hgap : FourierGap μ gap) : FourierGap (μ ∗ ν) gap := by
  intro s hs
  rw [fourierMoment_eq_charFun, charFun_conv, ← fourierMoment_eq_charFun μ,
    hgap s hs, zero_mul]

theorem convolution_apply_as_translations (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    {A : Set ℝ} (hA : MeasurableSet A) :
    (μ ∗ ν) A = ∫⁻ y, μ.map (fun x => x + y) A ∂ν := by
  rw [Measure.conv_comm, ← lintegral_indicator_one hA,
    Measure.lintegral_conv (show Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) from
      measurable_one.indicator hA)]
  apply lintegral_congr
  intro y
  rw [← lintegral_indicator_one hA, lintegral_map
    (show Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) from
      measurable_one.indicator hA) (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [add_comm]

/-- Only a central part of the convolution law is needed for minorization. -/
theorem convolution_minorization (μ ν ω : Measure ℝ) [SFinite μ] [SFinite ν]
    {S : Set ℝ} (hS : MeasurableSet S) {c : ℝ≥0∞}
    (hshift : ∀ y ∈ S, c • ω ≤ μ.map (fun x => x + y)) :
    (ν S * c) • ω ≤ μ ∗ ν := by
  apply Measure.le_iff.2
  intro A hA
  rw [convolution_apply_as_translations μ ν hA, Measure.smul_apply, smul_eq_mul]
  calc
    ν S * c * ω A = ∫⁻ y in S, c * ω A ∂ν := by
      rw [lintegral_const]
      simp only [Measure.restrict_apply_univ]
      ring
    _ ≤ ∫⁻ y in S, μ.map (fun x => x + y) A ∂ν := by
      apply setLIntegral_mono' hS
      intro y hy
      simpa only [Measure.smul_apply, smul_eq_mul] using (hshift y hy) A
    _ ≤ ∫⁻ y, μ.map (fun x => x + y) A ∂ν :=
      setLIntegral_le_lintegral _ _

/-- The normalized Lebesgue law on a closed interval. Endpoints have zero mass. -/
def intervalProbability (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Set.Icc a b)

theorem intervalProbability_isProbability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalProbability a b) := by
  constructor
  simp only [intervalProbability, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))
    ENNReal.ofReal_ne_top

theorem interval_restrict_le_translated {a b pad y : ℝ} (hy : |y| ≤ pad) :
    volume.restrict (Set.Icc a b) ≤
      (volume.restrict (Set.Icc (a - pad) (b + pad))).map (fun x => x + y) := by
  have hmap : volume.map (fun x : ℝ => x + y) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self y
  calc
    volume.restrict (Set.Icc a b) =
        (volume.restrict ((fun x : ℝ => x + y) ⁻¹' Set.Icc a b)).map
          (fun x => x + y) := by
      rw [← Measure.restrict_map (by fun_prop) measurableSet_Icc, hmap]
    _ ≤ _ := Measure.map_mono (Measure.restrict_mono_set volume (by
      intro x hx
      have hy' := abs_le.mp hy
      change a ≤ x + y ∧ x + y ≤ b at hx
      constructor <;> linarith [hx.1, hx.2])) (by fun_prop)

/-- Dividing the smaller and larger interval lengths gives the precise
minorization constant for each shift in the central kernel window. -/
theorem intervalProbability_le_translated {a b pad y : ℝ} (hab : a < b)
    (hpad : 0 ≤ pad) (hy : |y| ≤ pad) :
    (ENNReal.ofReal ((b - a) / (b - a + 2 * pad))) • intervalProbability a b ≤
      (intervalProbability (a - pad) (b + pad)).map (fun x => x + y) := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hlarge : 0 < b - a + 2 * pad := by positivity
  have hsmall : ENNReal.ofReal (b - a) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hlen
  have heq : ENNReal.ofReal ((b - a) / (b - a + 2 * pad)) *
      (ENNReal.ofReal (b - a))⁻¹ = (ENNReal.ofReal (b - a + 2 * pad))⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hlarge, div_eq_mul_inv]
    rw [mul_right_comm, ENNReal.mul_inv_cancel hsmall ENNReal.ofReal_ne_top, one_mul]
  unfold intervalProbability
  rw [smul_smul, heq, Measure.map_smul _ (by fun_prop)]
  have hlarge_eq : b + pad - (a - pad) = b - a + 2 * pad := by ring
  rw [hlarge_eq]
  apply Measure.le_iff.2
  intro A _
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact interval_restrict_le_translated hy

/-- The averaging law is an exact probability mixture once its uniform part
has been minorized. This introduces no new analytic hypothesis. -/
theorem probability_mixture_of_minorization (ν ω : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ω] {η : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1)
    (hminor : ENNReal.ofReal (1 - η) • ω ≤ ν) :
    ∃ τ : Measure ℝ, IsProbabilityMeasure τ ∧ predictionMixture ω τ η = ν := by
  let c : ℝ≥0∞ := ENNReal.ofReal (1 - η)
  let d : ℝ≥0∞ := ENNReal.ofReal η
  let τ := d⁻¹ • (ν - c • ω)
  have hd0 : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hη0
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (c • ω) := by
    constructor
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top
  have hdiff : (ν - c • ω) Set.univ = d := by
    rw [Measure.sub_apply MeasurableSet.univ hminor]
    simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one]
    dsimp only [c, d]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - η)]
    congr 1
    ring
  have hτ : IsProbabilityMeasure τ := by
    constructor
    change d⁻¹ * (ν - c • ω) Set.univ = 1
    rw [hdiff, ENNReal.inv_mul_cancel hd0 hdtop]
  refine ⟨τ, hτ, ?_⟩
  unfold predictionMixture
  change c • ω + d • (d⁻¹ • (ν - c • ω)) = ν
  rw [smul_smul, ENNReal.mul_inv_cancel hd0 hdtop, one_smul, add_comm]
  exact Measure.sub_add_cancel_of_le hminor

end LipschitzHilbert

end

end OAI
