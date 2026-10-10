import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

section

/-! # Integrating a nonnegative characteristic comparison on a finite time window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_eLpNorm_le {T : ℝ} (hT : 0 ≤ T)
    {F e : ℝ × P → ℝ} {d : P → ℝ}
    (hFm : Measurable F) (hem : Measurable e) (hdm : Measurable d)
    (he0 : ∀ z, 0 ≤ e z)
    (hei : Integrable e ((volume.restrict (Icc 0 T)).prod ν))
    (hb : ∀ t ∈ Icc 0 T, ∀ p, |F (t,p)| ≤ d p+∫ s in 0..t, e (s,p)) :
    eLpNorm F 1 ((volume.restrict (Icc 0 T)).prod ν) ≤
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 (volume.restrict (Icc 0 T))*
        (eLpNorm d 1 ν+eLpNorm e 1 ((volume.restrict (Icc 0 T)).prod ν)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let a : P → ℝ := fun p => ∫ s, e (s,p) ∂μ
  have ham : Measurable a := hem.stronglyMeasurable.integral_prod_left'.measurable
  have ha0 p : 0 ≤ a p := integral_nonneg (fun s => he0 (s,p))
  have ha : eLpNorm a 1 ν ≤ eLpNorm e 1 (μ.prod ν) := by
    have h := eLpNorm_integral_le (μ := ν) (ν := μ) (hem.comp measurable_swap)
    exact h.trans_eq (eLpNorm_comp_measurePreserving hem.aestronglyMeasurable
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)))
  have hbound : ∀ᵐ z ∂μ.prod ν, ‖F z‖ ≤ d z.2+a z.2 := by
    have ht : ∀ᵐ z ∂μ.prod ν, z.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    have hi : ∀ᵐ z ∂μ.prod ν, Integrable (fun s => e (s,z.2)) μ :=
      Measure.quasiMeasurePreserving_snd.ae hei.prod_left_ae
    filter_upwards [ht,hi] with z hz hzi
    have hint : IntervalIntegrable (fun s => e (s,z.2)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hzi
    have hm := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := z.1)
      (c := (0:ℝ)) (d := T) le_rfl hz.1 hz.2
      (ae_of_all _ (fun s => he0 (s,z.2))) hint
    have heq : (∫ s in 0..T, e (s,z.2)) = a z.2 := by
      rw [intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc]
    rw [heq] at hm
    have hb' : ‖F z‖ ≤ d z.2+∫ s in 0..z.1, e (s,z.2) := by
      simpa only [Real.norm_eq_abs] using hb z.1 hz z.2
    exact hb'.trans (add_le_add le_rfl hm)
  have hprod : eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) =
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ*eLpNorm (fun p => d p+a p) 1 ν := by
    simpa only [one_mul,Pi.add_apply] using eLpNorm_mul_prod_one
      (μ := μ) (ν := ν) (f := fun _ : ℝ => (1:ℝ)) (g := fun p => d p+a p)
      measurable_const (hdm.add ham)
  calc
    _ ≤ eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) :=
      eLpNorm_mono_ae_real hFm.aestronglyMeasurable hbound
    _ = _ := hprod
    _ ≤ _ := mul_le_mul' le_rfl ((eLpNorm_add_le (by norm_num)).trans (add_le_add le_rfl ha))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Integrating a nonnegative characteristic comparison on a finite time window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_ae_eLpNorm_le {T : ℝ} (hT : 0 ≤ T)
    {F e : ℝ × P → ℝ} {d : P → ℝ}
    (hFm : Measurable F) (hem : Measurable e) (hdm : Measurable d)
    (he0 : ∀ z, 0 ≤ e z)
    (hei : Integrable e ((volume.restrict (Icc 0 T)).prod ν))
    (hb : ∀ᵐ p ∂ν, ∀ t ∈ Icc 0 T, |F (t,p)| ≤ d p+∫ s in 0..t, e (s,p)) :
    eLpNorm F 1 ((volume.restrict (Icc 0 T)).prod ν) ≤
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 (volume.restrict (Icc 0 T))*
        (eLpNorm d 1 ν+eLpNorm e 1 ((volume.restrict (Icc 0 T)).prod ν)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let a : P → ℝ := fun p => ∫ s, e (s,p) ∂μ
  have ham : Measurable a := hem.stronglyMeasurable.integral_prod_left'.measurable
  have ha0 p : 0 ≤ a p := integral_nonneg (fun s => he0 (s,p))
  have ha : eLpNorm a 1 ν ≤ eLpNorm e 1 (μ.prod ν) := by
    have h := eLpNorm_integral_le (μ := ν) (ν := μ) (hem.comp measurable_swap)
    exact h.trans_eq (eLpNorm_comp_measurePreserving hem.aestronglyMeasurable
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)))
  have hbound : ∀ᵐ z ∂μ.prod ν, ‖F z‖ ≤ d z.2+a z.2 := by
    have ht : ∀ᵐ z ∂μ.prod ν, z.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    have hi : ∀ᵐ z ∂μ.prod ν, Integrable (fun s => e (s,z.2)) μ :=
      Measure.quasiMeasurePreserving_snd.ae hei.prod_left_ae
    filter_upwards [ht,hi,Measure.quasiMeasurePreserving_snd.ae hb] with z hz hzi hzb
    have hint : IntervalIntegrable (fun s => e (s,z.2)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hzi
    have hm := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := z.1)
      (c := (0:ℝ)) (d := T) le_rfl hz.1 hz.2
      (ae_of_all _ (fun s => he0 (s,z.2))) hint
    have heq : (∫ s in 0..T, e (s,z.2)) = a z.2 := by
      rw [intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc]
    rw [heq] at hm
    have hb' : ‖F z‖ ≤ d z.2+∫ s in 0..z.1, e (s,z.2) := by
      simpa only [Real.norm_eq_abs] using hzb z.1 hz
    exact hb'.trans (add_le_add le_rfl hm)
  have hprod : eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) =
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ*eLpNorm (fun p => d p+a p) 1 ν := by
    simpa only [one_mul,Pi.add_apply] using eLpNorm_mul_prod_one
      (μ := μ) (ν := ν) (f := fun _ : ℝ => (1:ℝ)) (g := fun p => d p+a p)
      measurable_const (hdm.add ham)
  calc
    _ ≤ eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) :=
      eLpNorm_mono_ae_real hFm.aestronglyMeasurable hbound
    _ = _ := hprod
    _ ≤ _ := mul_le_mul' le_rfl ((eLpNorm_add_le (by norm_num)).trans (add_le_add le_rfl ha))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Vanishing initial and source errors imply vanishing characteristic comparisons -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_ae_strongL1 {T : ℝ} (hT : 0 ≤ T)
    {F e : ℕ → ℝ × P → ℝ} {d : ℕ → P → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hem : ∀ n, Measurable (e n))
    (hdm : ∀ n, Measurable (d n)) (he0 : ∀ n z, 0 ≤ e n z)
    (hb : ∀ n, ∀ᵐ p ∂ν, ∀ t ∈ Icc 0 T, |F n (t,p)| ≤ d n p+∫ s in 0..t, e n (s,p))
    (hdt : Tendsto (fun n => eLpNorm (d n) 1 ν) atTop (𝓝 0))
    (het : Tendsto (fun n => eLpNorm (e n) 1 ((volume.restrict (Icc 0 T)).prod ν))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 1 ((volume.restrict (Icc 0 T)).prod ν)) atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hfinite : eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ ≠ ∞ :=
    (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ))).eLpNorm_ne_top
  have ht := ENNReal.Tendsto.const_mul (a := eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ)
    (hdt.add het) (Or.inr hfinite)
  simp only [zero_add,mul_zero] at ht
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht ε hε,
    ENNReal.tendsto_nhds_zero.mp het 1 (by norm_num)] with n hn hne
  have hi : Integrable (e n) (μ.prod ν) := memLp_one_iff_integrable.mp
    (show MemLp (e n) 1 (μ.prod ν) from hne.trans_lt (by simp))
  exact (prefixComparison_ae_eLpNorm_le hT (hFm n) (hem n) (hdm n) (he0 n) hi (hb n)).trans hn

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Vanishing initial and source errors imply vanishing characteristic comparisons -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_strongL1 {T : ℝ} (hT : 0 ≤ T)
    {F e : ℕ → ℝ × P → ℝ} {d : ℕ → P → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hem : ∀ n, Measurable (e n))
    (hdm : ∀ n, Measurable (d n)) (he0 : ∀ n z, 0 ≤ e n z)
    (hb : ∀ n t, t ∈ Icc 0 T → ∀ p, |F n (t,p)| ≤ d n p+∫ s in 0..t, e n (s,p))
    (hdt : Tendsto (fun n => eLpNorm (d n) 1 ν) atTop (𝓝 0))
    (het : Tendsto (fun n => eLpNorm (e n) 1 ((volume.restrict (Icc 0 T)).prod ν))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 1 ((volume.restrict (Icc 0 T)).prod ν)) atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hfinite : eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ ≠ ∞ :=
    (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ))).eLpNorm_ne_top
  have ht := ENNReal.Tendsto.const_mul (a := eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ)
    (hdt.add het) (Or.inr hfinite)
  simp only [zero_add,mul_zero] at ht
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht ε hε,
    ENNReal.tendsto_nhds_zero.mp het 1 (by norm_num)] with n hn hne
  have hi : Integrable (e n) (μ.prod ν) := memLp_one_iff_integrable.mp
    (show MemLp (e n) 1 (μ.prod ν) from hne.trans_lt (by simp))
  exact (prefixComparison_eLpNorm_le hT (hFm n) (hem n) (hdm n) (he0 n) hi (hb n)).trans hn

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
