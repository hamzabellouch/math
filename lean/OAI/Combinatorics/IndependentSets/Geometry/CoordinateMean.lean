import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.RowBitsEquiv

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def coordinateMean {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  ∫ t, f (Function.update x i t) ∂μ

noncomputable def influenceSq {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) : ℝ :=
  ∫ x, (f x-coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ)

lemma coordinateMean_measurable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} (hf : Measurable f) :
    Measurable (coordinateMean μ i f) :=
  (hf.comp (update_measurable i)).stronglyMeasurable.integral_prod_right'.measurable

lemma coordinateMean_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) (x : ι → α) : |coordinateMean μ i f x| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ:=μ) (f:=fun t => f (Function.update x i t))
    (C:=B) (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hb _))
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one, coordinateMean] using h

lemma coordinateMean_update {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) (x : ι → α) (t : α) :
    coordinateMean μ i f (Function.update x i t) = coordinateMean μ i f x := by
  simp only [coordinateMean, Function.update_idem]

lemma integral_mul_coordinateMean {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    (∫ x, f x * coordinateMean μ i f x ∂Measure.pi (fun _ : ι => μ)) =
      ∫ x, (coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  have hm := coordinateMean_measurable μ i hf
  have hi : Integrable (fun x => f x*coordinateMean μ i f x) (Measure.pi (fun _ : ι => μ)) :=
    bounded_integrable (hf.mul hm) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hb x) (coordinateMean_bound μ i hb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x)))
  rw [← integral_update μ i hi]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [coordinateMean_update, integral_mul_const]
  simp only [coordinateMean, sq]

theorem influenceSq_identity {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    influenceSq μ i f = (∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ)) -
      ∫ x, (coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  have hm := coordinateMean_measurable μ i hf
  have hmb := coordinateMean_bound μ i hb
  have hf2 := bounded_sq_integrable (μ:=Measure.pi (fun _ : ι => μ)) hf hb
  have hm2 := bounded_sq_integrable (μ:=Measure.pi (fun _ : ι => μ)) hm hmb
  have hprod : Integrable (fun x => f x*coordinateMean μ i f x) (Measure.pi (fun _ : ι => μ)) :=
    bounded_integrable (hf.mul hm) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hb x) (hmb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x)))
  unfold influenceSq
  have he (x : ι → α) : (f x-coordinateMean μ i f x)^2 =
      (f x)^2 - 2*(f x*coordinateMean μ i f x) + (coordinateMean μ i f x)^2 := by ring
  simp_rw [he]
  have hi2 : Integrable (fun x => (f x)^2 - 2*(f x*coordinateMean μ i f x)) (Measure.pi (fun _ : ι => μ)) := hf2.sub (hprod.const_mul 2)
  rw [integral_add hi2 hm2,
    integral_sub hf2 (hprod.const_mul 2), integral_const_mul,
    integral_mul_coordinateMean μ i hf hb]
  ring

lemma influenceSq_nonneg {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) : 0 ≤ influenceSq μ i f :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma influenceSq_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f : (ι → α) → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) :
    influenceSq μ i f ≤ ∫ x, (f x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  rw [influenceSq_identity μ i hf hb]
  have hn : 0 ≤ ∫ x : ι → α, (coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ) :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

lemma coordinateMean_sub {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (x : ι → α) : coordinateMean μ i (f-g) x = coordinateMean μ i f x-coordinateMean μ i g x := by
  apply integral_sub
  · exact bounded_integrable (hf.comp (by fun_prop)) (fun t => hb _)
  · exact bounded_integrable (hg.comp (by fun_prop)) (fun t => hc _)

lemma influenceSq_of_independent {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {f g : (ι → α) → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C)
    (hgind : ∀ x t, g (Function.update x i t) = g x) :
    influenceSq μ i f ≤ ∫ x, (f x-g x)^2 ∂Measure.pi (fun _ : ι => μ) := by
  have hgm (x : ι → α) : coordinateMean μ i g x = g x := by
    simp [coordinateMean, hgind]
  have hq : influenceSq μ i f = influenceSq μ i (f-g) := by
    unfold influenceSq
    apply integral_congr_ae
    filter_upwards [] with x
    rw [coordinateMean_sub μ i hf hg hb hc, hgm, Pi.sub_apply]
    congr 1
    ring
  rw [hq]
  exact influenceSq_le μ i (hf.sub hg)
    (fun x => (abs_sub _ _).trans (add_le_add (hb x) (hc x)))

end LargeIndependentSets.ProductAveraging

end OAI
