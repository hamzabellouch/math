import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.ProjectionTests

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
noncomputable def xlog (x : ℝ) : ℝ := x * Real.log x

lemma continuous_xlog : Continuous xlog := Real.continuous_mul_log
lemma xlog_zero : xlog 0 = 0 := by simp [xlog]
lemma xlog_one : xlog 1 = 0 := by simp [xlog]
lemma xlog_mul (x y : ℝ) : xlog (x*y) = y*xlog x+x*xlog y := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog_def, neg_mul] at h
  dsimp [xlog]
  linarith

lemma mul_log_div_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x/y) ≤ x^2/y-x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have h := Real.log_le_sub_one_of_pos (div_pos (lt_of_le_of_ne hx (Ne.symm hx0)) hy)
  have H := mul_le_mul_of_nonneg_left h hx
  simpa only [mul_sub, mul_one, pow_two, mul_div_assoc] using H

lemma xlog_lower_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    xlog y + (Real.log y+1)*(x-y) ≤ xlog x := by
  have h := Real.self_sub_one_le_mul_log (div_nonneg hx hy.le)
  by_cases hx0 : x = 0
  · simp only [hx0, xlog]
    nlinarith
  rw [Real.log_div hx0 hy.ne'] at h
  have H := mul_le_mul_of_nonneg_left h hy.le
  dsimp [xlog]
  field_simp at H
  nlinarith

lemma integrable_bounded_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hC x)

lemma integrable_xlog_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) : Integrable (fun x => xlog (p x)) μ := by
  have hr : Set.range p ⊆ Icc (0:ℝ) 1 := by rintro _ ⟨x,rfl⟩; exact ⟨hp0 x,hp1 x⟩
  obtain ⟨C,hC⟩ := (isCompact_Icc.image continuous_xlog).isBounded.exists_norm_le
  apply integrable_bounded_measurable μ _ (continuous_xlog.measurable.comp hp)
  intro x
  simpa only [Real.norm_eq_abs, Function.comp_apply] using
    hC _ (Set.mem_image_of_mem _ (hr (Set.mem_range_self x)))

noncomputable def scoreMass {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → ℝ) : ℝ :=
  ∫ x, p x ∂μ

noncomputable def infoContribution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) : ℝ :=
  (∫ x, xlog (p x) ∂μ) - xlog (scoreMass μ p)

lemma scoreMass_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) (hp0 : ∀ x, 0 ≤ p x) : 0 ≤ scoreMass μ p :=
  integral_nonneg hp0

lemma scoreMass_le_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) : scoreMass μ p ≤ 1 := by
  have hi := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  simpa [scoreMass] using integral_mono hi (integrable_const (1:ℝ)) hp1

lemma infoContribution_zero_mass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (hP : scoreMass μ p = 0) :
    infoContribution μ p = 0 := by
  have hi := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hz : p =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hp0 hi).mp hP
  have h : (fun x => xlog (p x)) =ᵐ[μ] 0 := by filter_upwards [hz] with x hx; simp [hx, xlog_zero]
  simp [infoContribution, hP, xlog_zero, integral_congr_ae h]

lemma infoContribution_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) : 0 ≤ infoContribution μ p := by
  have hP := scoreMass_nonneg μ p hp0
  by_cases hz : scoreMass μ p = 0
  · rw [infoContribution_zero_mass μ p hp hp0 hp1 hz]
  have hpos : 0 < scoreMass μ p := lt_of_le_of_ne hP (Ne.symm hz)
  have hip := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hil := integrable_xlog_probability μ p hp hp0 hp1
  have h := integral_mono ((integrable_const _).add
    ((hip.sub (integrable_const _)).const_mul _)) hil (fun x => xlog_lower_tangent (hp0 x) hpos)
  have hiq : Integrable (fun x => (Real.log (scoreMass μ p)+1)*(p x-scoreMass μ p)) μ :=
    (hip.sub (integrable_const _)).const_mul _
  have hadd := integral_add (integrable_const (xlog (scoreMass μ p))) hiq
  simp only [Pi.add_apply, Pi.sub_apply] at h hadd
  rw [hadd, integral_const_mul] at h
  have hsub := integral_sub hip (integrable_const (scoreMass μ p))
  rw [hsub] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, scoreMass,
    sub_self, mul_zero, add_zero] at h
  dsimp [infoContribution, scoreMass]
  linarith

lemma xlog_upper_quadratic {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    xlog x ≤ x^2/a + (Real.log a-1)*x := by
  by_cases hz : x = 0
  · simp [hz,xlog_zero]
  have h := mul_log_div_le hx ha
  rw [Real.log_div hz ha.ne'] at h
  dsimp [xlog]
  nlinarith

lemma infoContribution_le_log_l2bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {L : ℝ} (hL : 0 < L) (hbound : (∫ x, (p x)^2 ∂μ) ≤ L^2) :
    infoContribution μ p ≤ 2*scoreMass μ p*(Real.log L-Real.log (scoreMass μ p)) := by
  have hP := scoreMass_nonneg μ p hp0
  by_cases hz : scoreMass μ p = 0
  · rw [infoContribution_zero_mass μ p hp hp0 hp1 hz,hz]; simp
  have hpos : 0 < scoreMass μ p := lt_of_le_of_ne hP (Ne.symm hz)
  let A := L^2 / scoreMass μ p
  have ha : 0 < A := div_pos (sq_pos_of_pos hL) hpos
  have hip := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa only [abs_of_nonneg (hp0 x)] using hp1 x)
  have hi2 : Integrable (fun x => (p x)^2) μ := by
    apply integrable_bounded_measurable μ _ (hp.pow_const 2) (C := 1)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hp0 x,hp1 x]
  have hil := integrable_xlog_probability μ p hp hp0 hp1
  have h := integral_mono hil ((hi2.div_const A).add (hip.const_mul (Real.log A-1)))
    (fun x => xlog_upper_quadratic (hp0 x) ha)
  have heq : (∫ x, (p x)^2/A+(Real.log A-1)*p x ∂μ) =
      (∫ x, (p x)^2 ∂μ)/A+(Real.log A-1)*scoreMass μ p := by
    rw [integral_add (hi2.div_const A) (hip.const_mul _),integral_div,integral_const_mul]
    rfl
  change (∫ x, xlog (p x) ∂μ) ≤ (∫ x, (p x)^2/A+(Real.log A-1)*p x ∂μ) at h
  rw [heq] at h
  have hb : (∫ x, (p x)^2 ∂μ)/A ≤ scoreMass μ p := by
    have h := div_le_div_of_nonneg_right hbound ha.le
    have he : L^2/A = scoreMass μ p := by dsimp [A]; field_simp
    exact he ▸ h
  have hlog : Real.log A = 2*Real.log L-Real.log (scoreMass μ p) := by
    simp [A,Real.log_div (pow_ne_zero _ hL.ne') hz,Real.log_pow]
  change (∫ x, xlog (p x) ∂μ) - scoreMass μ p * Real.log (scoreMass μ p) ≤ _
  rw [hlog] at h
  nlinarith

lemma log_ratio_lower {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 < P) (hz : b = 0 → a = 0) :
    a*(Real.log P+1)-P*b ≤ a*Real.log (a/b) := by
  by_cases hb0 : b = 0
  · simp [hb0,hz hb0]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have h := xlog_lower_tangent (div_nonneg ha hb) hP
  have H := mul_le_mul_of_nonneg_left h hb
  dsimp [xlog] at H
  field_simp at H
  nlinarith

lemma finite_log_sum {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hb1 : ∑ i,b i = 1)
    (hz : ∀ i, b i = 0 → a i = 0) :
    xlog (∑ i,a i) ≤ ∑ i,a i * Real.log (a i/b i) := by
  have hA : 0 ≤ ∑ i,a i := Finset.sum_nonneg (fun i _ => ha i)
  by_cases h0 : ∑ i,a i = 0
  · have hall : ∀ i, a i = 0 := fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp h0 i (Finset.mem_univ i)
    simp [hall,xlog_zero]
  have hAp : 0 < ∑ i,a i := lt_of_le_of_ne hA (Ne.symm h0)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => log_ratio_lower (ha i) (hb i) hAp (hz i))
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,hb1,mul_one] at h
  dsimp [xlog]
  nlinarith

lemma log_ratio_mul {a b : ℝ} (hb : b ≠ 0) :
    a*Real.log (a/b) = xlog a-a*Real.log b := by
  by_cases ha : a = 0
  · simp [ha,xlog_zero]
  rw [Real.log_div ha hb]
  simp [xlog,mul_sub]

lemma neg_xlog_le_one {x : ℝ} (hx : 0 ≤ x) : -xlog x ≤ 1 := by
  have h := Real.self_sub_one_le_mul_log hx
  dsimp [xlog]
  linarith

lemma xlog_nonpos {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : xlog x ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos hx (Real.log_nonpos hx hx1)

lemma finite_entropy_mass_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    -(∑ i,xlog (a i)) ≤ (∑ i,a i)*Real.log (Fintype.card ι)-xlog (∑ i,a i) := by
  have hN : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := finite_log_sum a (fun _ => 1/(Fintype.card ι:ℝ)) ha
    (fun _ => by positivity) (by simp [hN.ne']) (fun _ hz => (ne_of_gt (one_div_pos.mpr hN) hz).elim)
  simp_rw [log_ratio_mul (by positivity : 1/(Fintype.card ι:ℝ) ≠ 0),Real.log_div one_ne_zero hN.ne',Real.log_one,zero_sub,
    mul_neg,sub_neg_eq_add,Finset.sum_add_distrib,← Finset.sum_mul] at h
  linarith

end RepeatedLocalization

end OAI
