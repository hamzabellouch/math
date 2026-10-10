import OAI.Probability.BenjaminiSchramm.BlockExposure
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_lintegral_rpow_le_rpow_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    (∫⁻ ω, f ω ^ b ∂μ) ≤ (∫⁻ ω, f ω ∂μ)^b := by
  by_cases he : b = 1
  · simp only [he,ENNReal.rpow_one,le_refl]
  have hblt : b < 1 := lt_of_le_of_ne hb1 he
  have hc := Real.holderConjugate_one_div hb (sub_pos.mpr hblt) (by ring : b+(1-b)=1)
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    ((hf.pow_const b).aemeasurable) (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) μ)
  have hcancel : b*(1/b)=1 := by field_simp
  have hinv : 1/(1/b)=b := by field_simp
  simpa only [Pi.mul_apply,mul_one,ENNReal.one_rpow,←ENNReal.rpow_mul,hcancel,ENNReal.rpow_one,
    lintegral_const,measure_univ,one_mul,hinv] using hh

lemma ennreal_fractional_finset_sum {ι : Type*} (F : Finset ι) (f : ι → ℝ≥0∞)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑ z ∈ F, f z)^a ≤ ∑ z ∈ F, f z^a := by
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,ENNReal.zero_rpow_of_pos ha,le_refl]
  | @insert z F hz ih =>
    simp only [Finset.sum_insert hz]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1).trans (add_le_add le_rfl ih)

theorem fractional_frontier_continuations
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Finset ι) (f : ι → Ω → ℝ≥0∞) (hf : ∀ z ∈ F, Measurable (f z))
    (g : Ω → ℝ≥0∞) (hcover : ∀ ω, g ω ≤ ∑ z ∈ F, f z ω)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (L : ℝ≥0∞) (hL : ∀ z ∈ F, (∫⁻ ω, f z ω^a ∂μ) ≤ L) :
    (∫⁻ ω, g ω^(a*b) ∂μ) ≤ (F.card : ℝ≥0∞)^b*L^b := by
  have hm : Measurable (fun ω => ∑ z ∈ F, f z ω^a) :=
    Finset.measurable_sum F (fun z hz => (hf z hz).pow_const a)
  calc
    _ ≤ ∫⁻ ω, (∑ z ∈ F, f z ω^a)^b ∂μ := by
      apply lintegral_mono
      intro ω
      change g ω^(a*b) ≤ (∑ z ∈ F, f z ω^a)^b
      rw [ENNReal.rpow_mul]
      exact ENNReal.rpow_le_rpow
        ((ENNReal.rpow_le_rpow (hcover ω) ha.le).trans
          (ennreal_fractional_finset_sum F (fun z => f z ω) ha ha1)) hb.le
    _ ≤ (∫⁻ ω, ∑ z ∈ F, f z ω^a ∂μ)^b :=
      ennreal_lintegral_rpow_le_rpow_lintegral μ _ hm hb hb1
    _ = (∑ z ∈ F, ∫⁻ ω, f z ω^a ∂μ)^b := by
      rw [lintegral_finsetSum F (fun z hz => (hf z hz).pow_const a)]
    _ ≤ ((F.card : ℝ≥0∞)*L)^b := by
      apply ENNReal.rpow_le_rpow _ hb.le
      calc
        _ ≤ ∑ _z ∈ F, L := Finset.sum_le_sum hL
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hb.le

theorem exposed_frontier_fractional_bound {E ι : Type*}
    (q : E → unitInterval) (Q : Set E) (A : Set (Set E))
    (hA : MeasurableSet A) (hAdep : DependsOn (fun ω => ω ∈ A) Q)
    (F : Finset ι) (f : ι → Set E → ℝ≥0∞) (hf : ∀ z ∈ F, Measurable (f z))
    (g : Set E → ℝ≥0∞) (hg : Measurable g) (hgdep : DependsOn g Qᶜ)
    (hcover : ∀ ω, g ω ≤ ∑ z ∈ F, f z ω)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (L : ℝ≥0∞) (hL : ∀ z ∈ F,
      (∫⁻ ω, f z ω^a ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, A.indicator (fun ω => g ω^(a*b)) ω ∂CriticalPercolation.BernoulliProduct.law q) ≤
      CriticalPercolation.BernoulliProduct.law q A * (F.card : ℝ≥0∞)^b*L^b := by
  rw [CriticalPercolation.BernoulliProduct.lintegral_indicator_fresh q Q A hA hAdep _
    (hg.pow_const (a*b)) (fun ω η h => congrArg (fun x : ℝ≥0∞ => x^(a*b)) (hgdep h))]
  exact (mul_le_mul' le_rfl (fractional_frontier_continuations
    (CriticalPercolation.BernoulliProduct.law q) F f hf g hcover ha ha1 hb hb1 L hL)).trans_eq
      (mul_assoc _ _ _).symm

end Percolation.BenjaminiSchramm

end

end OAI
