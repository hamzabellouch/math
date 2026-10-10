import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! Moment bounds survive finite positive convex combinations and
almost-sure limits. These two steps preserve the actual level bounds. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped ENNReal Topology

namespace SLEExactGauge

lemma ofReal_pow_convex_sum_le {ι : Type*} (s : Finset ι)
    (w a : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1)
    (ha : ∀ i ∈ s, 0 ≤ a i) (m : ℕ) :
    ENNReal.ofReal (∑ i ∈ s, w i*a i)^m ≤
      ∑ i ∈ s, ENNReal.ofReal (w i) * ENNReal.ofReal (a i)^m := by
  have hs : 0 ≤ ∑ i ∈ s, w i*a i := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (ha i hi))
  rw [← ENNReal.ofReal_pow hs]
  apply (ENNReal.ofReal_le_ofReal (Real.pow_arith_mean_le_arith_mean_pow s w a hw hw₁ ha m)).trans_eq
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (hw i hi) (pow_nonneg (ha i hi) m))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.ofReal_mul (hw i hi),ENNReal.ofReal_pow (ha i hi)]

lemma lintegral_pow_convex_sum_le
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ι) (w : ι → ℝ) (a : ι → Ω → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1)
    (ha : ∀ i ∈ s, ∀ ω, 0 ≤ a i ω) (ham : ∀ i ∈ s, Measurable (a i))
    (m : ℕ) (M : ℝ≥0∞) (hM : ∀ i ∈ s, (∫⁻ ω, ENNReal.ofReal (a i ω)^m ∂P) ≤ M) :
    (∫⁻ ω, ENNReal.ofReal (∑ i ∈ s, w i*a i ω)^m ∂P) ≤ M := by
  calc
    _ ≤ ∫⁻ ω, ∑ i ∈ s, ENNReal.ofReal (w i) * ENNReal.ofReal (a i ω)^m ∂P :=
      lintegral_mono (fun ω => ofReal_pow_convex_sum_le s w (fun i => a i ω) hw hw₁
        (fun i hi => ha i hi ω) m)
    _ = ∑ i ∈ s, ENNReal.ofReal (w i) * ∫⁻ ω, ENNReal.ofReal (a i ω)^m ∂P := by
      rw [lintegral_finsetSum s (f := fun i ω => ENNReal.ofReal (w i) * ENNReal.ofReal (a i ω)^m)
        (fun i hi => measurable_const.mul ((ham i hi).ennreal_ofReal.pow_const m))]
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (w i) * M :=
      Finset.sum_le_sum (fun i hi => mul_le_mul' le_rfl (hM i hi))
    _ = M := by
      rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg hw,hw₁,ENNReal.ofReal_one,one_mul]

lemma lintegral_le_of_ae_tendsto_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (F : Ω → ℝ≥0∞)
    (hf : ∀ n, AEMeasurable (f n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)))
    (M : ℝ≥0∞) (hM : ∀ n, (∫⁻ ω, f n ω ∂P) ≤ M) :
    (∫⁻ ω, F ω ∂P) ≤ M := by
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with ω hω
      exact hω.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hf
    _ ≤ M := by
      have h : ∀ᶠ n : ℕ in atTop, (∫⁻ ω, f n ω ∂P) ≤ M := Eventually.of_forall hM
      simpa only [liminf_const] using liminf_le_liminf h

end SLEExactGauge

end

end OAI
