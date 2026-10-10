import OAI.Probability.SLE.Multipoint.MultipointPiecewiseClock

namespace OAI

/-! Integrating finitely many active-interval costs. The interval endpoints
may be different for every point or pair. -/

noncomputable section
open Set Filter MeasureTheory

namespace SLEExactGauge.Multipoint

lemma active_interval_integral (f : ℝ → ℝ) {a b H : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ H) :
    (∫ t in 0..H, (Ioc a b).indicator f t) = ∫ t in a..b, f t := by
  have h0H := ha.trans (hab.trans hb)
  rw [intervalIntegral.integral_of_le h0H, MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  rw [inter_eq_left.mpr (Ioc_subset_Ioc ha hb)]
  exact (intervalIntegral.integral_of_le hab).symm

lemma active_interval_integrable (f : ℝ → ℝ) {a b H : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable ((Ioc a b).indicator f) volume 0 H :=
  ((integrable_indicator_iff measurableSet_Ioc).mpr hf.1).intervalIntegrable

theorem finite_active_cost_integral_le {ι : Type*}
    (s : Finset ι) (a b B : ι → ℝ) (f : ι → ℝ → ℝ) (H : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (hb : ∀ i ∈ s, b i ≤ H)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume (a i) (b i))
    (hB : ∀ i ∈ s, (∫ t in a i..b i, f i t) ≤ B i) :
    (∫ t in 0..H, ∑ i ∈ s, (Ioc (a i) (b i)).indicator (f i) t) ≤ ∑ i ∈ s, B i := by
  rw [intervalIntegral.integral_finsetSum
    (fun i hi => active_interval_integrable (f i) (hf i hi))]
  apply Finset.sum_le_sum
  intro i hi
  rw [active_interval_integral (f i) (ha i hi) (hab i hi) (hb i hi)]
  exact hB i hi

theorem dominated_active_cost_integral_le {ι : Type*}
    (s : Finset ι) (a b B : ι → ℝ) (f : ι → ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (hb : ∀ i ∈ s, b i ≤ H)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume (a i) (b i))
    (hB : ∀ i ∈ s, (∫ t in a i..b i, f i t) ≤ B i)
    (R : ℝ → ℝ) (hR : IntervalIntegrable R volume 0 H)
    (hle : R ≤ᵐ[volume.restrict (Icc 0 H)]
      (fun t => ∑ i ∈ s, (Ioc (a i) (b i)).indicator (f i) t)) :
    (∫ t in 0..H, R t) ≤ ∑ i ∈ s, B i := by
  have hsum : IntervalIntegrable
      (fun t => ∑ i ∈ s, (Ioc (a i) (b i)).indicator (f i) t) volume 0 H :=
    by
      convert (IntervalIntegrable.sum (a := 0) (b := H) s
        (fun i hi => active_interval_integrable (f i) (hf i hi))) using 1
      ext t
      simp only [Finset.sum_apply]
  exact (intervalIntegral.integral_mono_ae_restrict hH hR hsum hle).trans
    (finite_active_cost_integral_le s a b B f H ha hab hb hf hB)

end SLEExactGauge.Multipoint

end

end OAI
