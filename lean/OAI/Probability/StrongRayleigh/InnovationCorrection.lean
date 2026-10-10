import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Problem336AdditiveD139.InnovationCorrection

def correction (x : ℝ) (b : ℝ → ℝ) (u v : ℝ) : ℝ :=
  (v - u) * x - ∫ s in u..v, b s

theorem integral_mem_unitInterval_scaled {b : ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hb : ∀ s ∈ Icc u v, b s ∈ Icc (0 : ℝ) 1) :
    (∫ s in u..v, b s) ∈ Icc (0 : ℝ) (v - u) := by
  constructor
  · exact intervalIntegral.integral_nonneg huv (fun s hs => (hb s hs).1)
  · have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := v) (C := (1 : ℝ)) (f := b) (by
        intro s hs
        rw [uIoc_of_le huv] at hs
        have h := hb s (Ioc_subset_Icc_self hs)
        simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)
    have hnonneg := intervalIntegral.integral_nonneg (μ := volume) huv (fun s hs => (hb s hs).1)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg (sub_nonneg.mpr huv)] using hnorm

theorem abs_correction_le {x : ℝ} {b : ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hx : x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ s ∈ Icc u v, b s ∈ Icc (0 : ℝ) 1) :
    |correction x b u v| ≤ v - u := by
  have hi := integral_mem_unitInterval_scaled huv hb
  have h0 : 0 ≤ (v - u) * x := mul_nonneg (sub_nonneg.mpr huv) hx.1
  have h1 : (v - u) * x ≤ v - u := by
    simpa using mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr huv)
  rw [correction, abs_le]
  constructor <;> linarith [hi.1, hi.2]

theorem correction_eq_integral {x : ℝ} {b : ℝ → ℝ} {u v : ℝ}
    (hb : IntervalIntegrable b volume u v) :
    correction x b u v = ∫ s in u..v, x - b s := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const hb]
  simp [correction]

theorem abs_sum_correction_le {I : Type u_1} (S : Finset I) (θ x : I → ℝ)
    (b : I → ℝ → ℝ) {u v : ℝ} (huv : u ≤ v)
    (hx : ∀ i ∈ S, x i ∈ Icc (0 : ℝ) 1)
    (hb : ∀ i ∈ S, ∀ s ∈ Icc u v, b i s ∈ Icc (0 : ℝ) 1) :
    |∑ i ∈ S, θ i * correction (x i) (b i) u v| ≤
      (v - u) * ∑ i ∈ S, |θ i| := by
  calc
    |∑ i ∈ S, θ i * correction (x i) (b i) u v| ≤
        ∑ i ∈ S, |θ i * correction (x i) (b i) u v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |θ i| * (v - u) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_correction_le huv (hx i hi) (hb i hi)) (abs_nonneg _)
    _ = (v - u) * ∑ i ∈ S, |θ i| := by
      rw [← Finset.sum_mul, mul_comm]

def innovation (x : ℝ) (B b : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * x + B t - ∫ s in 0..t, b s

theorem innovation_sub_eq {x : ℝ} {B b : ℝ → ℝ} {u v : ℝ}
    (hbu : IntervalIntegrable b volume 0 u)
    (hbuv : IntervalIntegrable b volume u v) :
    innovation x B b v - innovation x B b u =
      (B v - B u) + correction x b u v := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals hbu hbuv
  simp only [innovation, correction]
  rw [← hadd]
  ring

theorem sum_innovation_sub_eq {I : Type u_2} (S : Finset I) (θ x : I → ℝ)
    (B b : I → ℝ → ℝ) {u v : ℝ}
    (hbu : ∀ i ∈ S, IntervalIntegrable (b i) volume 0 u)
    (hbuv : ∀ i ∈ S, IntervalIntegrable (b i) volume u v) :
    (∑ i ∈ S, θ i * (innovation (x i) (B i) (b i) v -
      innovation (x i) (B i) (b i) u)) =
    (∑ i ∈ S, θ i * (B i v - B i u)) +
      ∑ i ∈ S, θ i * correction (x i) (b i) u v := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [innovation_sub_eq (hbu i hi) (hbuv i hi), mul_add]

theorem intervalIntegrable_of_measurable_unitInterval {b : ℝ → ℝ}
    (hbm : Measurable b) (hb : ∀ s, b s ∈ Icc (0 : ℝ) 1) (u v : ℝ) :
    IntervalIntegrable b volume u v := by
  rw [intervalIntegrable_iff, uIoc]
  exact (integrable_const (1 : ℝ)).mono' hbm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hb s).1] using (hb s).2)

section RandomVariables

variable {Ω : Type u_3} [MeasurableSpace Ω]

theorem measurable_intervalIntegral {b : Ω → ℝ → ℝ}
    (hb : Measurable (Function.uncurry b)) (u v : ℝ) :
    Measurable (fun ω => ∫ s in u..v, b ω s) := by
  unfold intervalIntegral
  exact (hb.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Ioc u v))).measurable.sub
    (hb.stronglyMeasurable.integral_prod_right
      (ν := volume.restrict (Ioc v u))).measurable

theorem measurable_correction {x : Ω → ℝ} {b : Ω → ℝ → ℝ}
    (hx : Measurable x) (hb : Measurable (Function.uncurry b)) (u v : ℝ) :
    Measurable (fun ω => correction (x ω) (b ω) u v) :=
  (measurable_const.mul hx).sub (measurable_intervalIntegral hb u v)

theorem integrable_correction_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {x : Ω → ℝ} {b : Ω → ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hxm : Measurable x) (hbm : Measurable (Function.uncurry b))
    (hx : ∀ ω, x ω ∈ Icc (0 : ℝ) 1)
    (hb : ∀ ω, ∀ s ∈ Icc u v, b ω s ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun ω => correction (x ω) (b ω) u v ^ n) μ := by
  apply (integrable_const ((v - u) ^ n)).mono'
    ((measurable_correction hxm hbm u v).pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_correction_le huv (hx ω) (hb ω)) n

theorem integrable_abs_correction_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {x : Ω → ℝ} {b : Ω → ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hxm : Measurable x) (hbm : Measurable (Function.uncurry b))
    (hx : ∀ ω, x ω ∈ Icc (0 : ℝ) 1)
    (hb : ∀ ω, ∀ s ∈ Icc u v, b ω s ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun ω => |correction (x ω) (b ω) u v| ^ n) μ := by
  simpa only [abs_pow] using (integrable_correction_pow μ huv hxm hbm hx hb n).abs

theorem measurable_sum_correction {I : Type u_4} (S : Finset I) (θ : I → ℝ)
    {x : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ}
    (hx : ∀ i ∈ S, Measurable (x i))
    (hb : ∀ i ∈ S, Measurable (Function.uncurry (b i))) (u v : ℝ) :
    Measurable (fun ω => ∑ i ∈ S, θ i * correction (x i ω) (b i ω) u v) := by
  exact S.measurable_sum (fun i hi => measurable_const.mul
    (measurable_correction (hx i hi) (hb i hi) u v))

theorem integrable_sum_correction_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {I : Type u_5} (S : Finset I) (θ : I → ℝ)
    {x : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ} {u v : ℝ}
    (huv : u ≤ v) (hxm : ∀ i ∈ S, Measurable (x i))
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hx : ∀ i ∈ S, ∀ ω, x i ω ∈ Icc (0 : ℝ) 1)
    (hb : ∀ i ∈ S, ∀ ω, ∀ s ∈ Icc u v, b i ω s ∈ Icc (0 : ℝ) 1)
    (n : ℕ) :
    Integrable (fun ω => (∑ i ∈ S, θ i * correction (x i ω) (b i ω) u v) ^ n) μ := by
  apply (integrable_const (((v - u) * ∑ i ∈ S, |θ i|) ^ n)).mono'
    ((measurable_sum_correction S θ hxm hbm u v).pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_sum_correction_le S θ (fun i => x i ω) (fun i => b i ω) huv
      (fun i hi => hx i hi ω) (fun i hi => hb i hi ω)) n

end RandomVariables

end Problem336AdditiveD139.InnovationCorrection

end

end OAI
