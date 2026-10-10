import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyAverageMoment

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def cappedMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (L : ℝ) : ℝ := ∫ x, (min (X x) L)^2 ∂μ
noncomputable def cappedTailMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (A L : ℝ) : ℝ := ∫ x, (if A < X x then (min (X x) L)^2 else 0) ∂μ

lemma min_rescale {L : ℝ} (hL : 0 < L) (x : ℝ) : min x L = L*min (x/L) 1 := by
  rw [← div_self (ne_of_gt hL),min_div_div_right hL.le]
  field_simp

lemma cappedMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) {L : ℝ} (hL : 0 < L) :
    cappedMoment μ X L = L^2*cappedMoment μ (fun x => X x/L) 1 := by
  unfold cappedMoment
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [min_rescale hL]
  ring

lemma cappedTailMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (A : ℝ) {L : ℝ} (hL : 0 < L) :
    cappedTailMoment μ X A L = L^2*cappedTailMoment μ (fun x => X x/L) (A/L) 1 := by
  unfold cappedTailMoment
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [div_lt_div_iff_of_pos_right hL]
  split_ifs
  · rw [min_rescale hL]; ring
  · ring

lemma cappedMoment_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) :
    0 ≤ cappedMoment μ X 1 ∧ cappedMoment μ X 1 ≤ 1 := by
  have hb (x) : 0 ≤ (min (X x) 1)^2 ∧ (min (X x) 1)^2 ≤ 1 := by
    have h0 := le_min (hX0 x) zero_le_one
    have h1 := min_le_right (X x) 1
    constructor <;> nlinarith
  have hi : Integrable (fun x => (min (X x) 1)^2) μ :=
    (integrable_const (1:ℝ)).mono' ((hX.min measurable_const).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2))
  constructor
  · exact integral_nonneg (fun x => (hb x).1)
  · calc
      _ ≤ ∫ x, (1:ℝ) ∂μ := integral_mono hi (integrable_const _) (fun x => (hb x).2)
      _ = 1 := by simp

lemma cappedTailMoment_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) (A : ℝ) :
    0 ≤ cappedTailMoment μ X A 1 ∧ cappedTailMoment μ X A 1 ≤ 1 := by
  let f := fun x => if A < X x then (min (X x) 1)^2 else 0
  have hb (x) : 0 ≤ f x ∧ f x ≤ 1 := by
    have h0 := le_min (hX0 x) zero_le_one
    have h1 := min_le_right (X x) 1
    dsimp [f]
    split_ifs <;> constructor <;> nlinarith
  have hm : Measurable f := Measurable.ite (measurableSet_lt measurable_const hX)
    ((hX.min measurable_const).pow_const 2) measurable_const
  have hi : Integrable f μ := (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2))
  constructor
  · exact integral_nonneg (fun x => (hb x).1)
  · calc
      _ ≤ ∫ x, (1:ℝ) ∂μ := integral_mono hi (integrable_const _) (fun x => (hb x).2)
      _ = 1 := by simp

lemma limsup_cappedMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hX0 : ∀ n x, 0 ≤ X n x) {L : ℝ} (hL : 0 < L) :
    limsup (fun n => cappedMoment (μ n) (X n) L) atTop =
    L^2*limsup (fun n => cappedMoment (μ n) (fun x => X n x/L) 1) atTop := by
  simp only [cappedMoment_scale _ _ hL]
  apply limsup_nonneg_const_mul _ (sq_nonneg L)
    (fun n => (cappedMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le)).1)
    (fun n => (cappedMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le)).2)

lemma limsup_cappedTailMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hX0 : ∀ n x, 0 ≤ X n x) (A : ℝ) {L : ℝ} (hL : 0 < L) :
    limsup (fun n => cappedTailMoment (μ n) (X n) A L) atTop =
    L^2*limsup (fun n => cappedTailMoment (μ n) (fun x => X n x/L) (A/L) 1) atTop := by
  simp only [cappedTailMoment_scale _ _ _ hL]
  apply limsup_nonneg_const_mul _ (sq_nonneg L)
    (fun n => (cappedTailMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le) _).1)
    (fun n => (cappedTailMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le) _).2)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma cappedMoment_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) {B : ℝ} (hB : 0 < B) :
    0 ≤ cappedMoment μ X B ∧ cappedMoment μ X B ≤ B^2 := by
  rw [cappedMoment_scale μ X hB]
  have hh := cappedMoment_unit_bounds μ (fun x => X x/B) (hX.div_const B)
    (fun x => div_nonneg (hX0 x) hB.le)
  constructor
  · exact mul_nonneg (sq_nonneg B) hh.1
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 (sq_nonneg B)

lemma cappedMoment_descaled {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {r B : ℝ} (hr : 0 < r) :
    (∫ x, (min (X x) (B*r))^2 ∂μ)=r^2*cappedMoment μ (fun x => X x/r) B := by
  rw [cappedMoment,←integral_const_mul]
  congr 1
  funext x
  have hh : min (X x) (B*r) = r*min (X x/r) B := by
    rw [mul_min_of_nonneg _ _ hr.le,mul_div_cancel₀ _ hr.ne',mul_comm r B]
  rw [hh]
  ring
lemma cappedTailMoment_descaled {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {r A B : ℝ} (hr : 0 < r) :
    (∫ x, (if A*r < X x then (min (X x) (B*r))^2 else 0) ∂μ)=
      r^2*cappedTailMoment μ (fun x => X x/r) A B := by
  rw [cappedTailMoment,←integral_const_mul]
  congr 1
  funext x
  simp only [lt_div_iff₀ hr]
  split_ifs
  · have hh : min (X x) (B*r) = r*min (X x/r) B := by
      rw [mul_min_of_nonneg _ _ hr.le,mul_div_cancel₀ _ hr.ne',mul_comm r B]
    rw [hh]
    ring
  · ring
lemma cappedTailMoment_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    0 ≤ cappedTailMoment μ X A B ∧ cappedTailMoment μ X A B ≤ B^2 := by
  rw [cappedTailMoment_scale μ X A hB]
  have hh := cappedTailMoment_unit_bounds μ (fun x => X x/B) (hX.div_const B)
    (fun x => div_nonneg (hX0 x) hB.le) (A/B)
  constructor
  · exact mul_nonneg (sq_nonneg B) hh.1
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 (sq_nonneg B)
end DirectionalTransience

end

end

end OAI
