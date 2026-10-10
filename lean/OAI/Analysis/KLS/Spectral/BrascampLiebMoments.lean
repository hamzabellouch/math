import OAI.Analysis.KLS.Measures.PotentialMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace LeanBlast.KLS

section BoundedKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {h q : α → ℝ} {B : ℝ}

private theorem boundedKernel_bound (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)) (B : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a ∈ Icc (-B) B, ∀ b ∈ Icc (-B) B,
      ‖Φ t a b‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hΦ.continuousOn
  exact ⟨C, fun t ht a ha b hb => hC (t, a, b) ⟨ht, ha, hb⟩⟩

theorem boundedKernel_integrable (Φ : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2))
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun x => Φ t (h x) (q x)) μ := by
  obtain ⟨C, hC⟩ := boundedKernel_bound Φ hΦ B
  apply (integrable_const C).mono'
    (hΦ.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  exact ae_of_all _ fun x => hC t ht (h x) (abs_le.mp (hhB x)) (q x) (abs_le.mp (hqB x))

theorem boundedKernel_hasDerivAt_integral (Φ Φ' : ℝ → ℝ → ℝ → ℝ)
    (hΦ : Continuous (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2))
    (hΦ' : Continuous (fun p : ℝ × ℝ × ℝ => Φ' p.1 p.2.1 p.2.2))
    (hd : ∀ t a b, HasDerivAt (fun s => Φ s a b) (Φ' t a b) t)
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => ∫ x, Φ s (h x) (q x) ∂μ)
      (∫ x, Φ' t (h x) (q x) ∂μ) t := by
  obtain ⟨C, hC⟩ := boundedKernel_bound Φ' hΦ' B
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s x => Φ s (h x) (q x))
    (F' := fun s x => Φ' s (h x) (q x))
    (bound := fun _ : α => C) (Ioo_mem_nhds ht.1 ht.2) ?_
    (boundedKernel_integrable Φ hΦ hh hq hhB hqB ⟨ht.1.le, ht.2.le⟩) ?_ ?_
    (integrable_const C) ?_).2
  · exact Eventually.of_forall fun s =>
      (hΦ.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  · exact (hΦ'.measurable.comp (measurable_const.prodMk (hh.prodMk hq))).aestronglyMeasurable
  · exact ae_of_all _ fun x s hs =>
      hC s ⟨hs.1.le, hs.2.le⟩ (h x) (abs_le.mp (hhB x)) (q x) (abs_le.mp (hqB x))
  · exact ae_of_all _ fun x s _ => hd s (h x) (q x)

end BoundedKernel

def blWeight (t a b : ℝ) : ℝ := Real.exp (-t * a - t ^ 2 / 2 * b)

def blWeightDeriv (t a b : ℝ) : ℝ := (-a - t * b) * blWeight t a b

def blWeightSecond (t a b : ℝ) : ℝ := ((a + t * b) ^ 2 - b) * blWeight t a b

theorem continuous_blWeight :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeight p.1 p.2.1 p.2.2) := by
  unfold blWeight
  fun_prop

theorem continuous_blWeightDeriv :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeightDeriv p.1 p.2.1 p.2.2) := by
  unfold blWeightDeriv blWeight
  fun_prop

theorem continuous_blWeightSecond :
    Continuous (fun p : ℝ × ℝ × ℝ => blWeightSecond p.1 p.2.1 p.2.2) := by
  unfold blWeightSecond blWeight
  fun_prop

theorem hasDerivAt_blWeight (t a b : ℝ) :
    HasDerivAt (fun s => blWeight s a b) (blWeightDeriv t a b) t := by
  have h := ((((hasDerivAt_id' t).fun_neg.mul_const a).fun_sub
    (((hasDerivAt_id' t).fun_pow 2).div_const 2 |>.mul_const b))).exp
  convert h using 1 <;> dsimp [blWeight, blWeightDeriv]
  ring

theorem hasDerivAt_blWeightDeriv (t a b : ℝ) :
    HasDerivAt (fun s => blWeightDeriv s a b) (blWeightSecond t a b) t := by
  have h := ((hasDerivAt_const t (-a)).fun_sub ((hasDerivAt_id' t).mul_const b)).fun_mul
    (hasDerivAt_blWeight t a b)
  convert h using 1 <;> dsimp [blWeightSecond, blWeightDeriv]
  ring

section Moments

variable {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
  (h q : Space n → ℝ)

def blMoment (t : ℝ) : ℝ := ∫ x, blWeight t (h x) (q x) ∂μ
def blMomentDeriv (t : ℝ) : ℝ := ∫ x, blWeightDeriv t (h x) (q x) ∂μ
def blMomentSecond (t : ℝ) : ℝ := ∫ x, blWeightSecond t (h x) (q x) ∂μ
def blLogMoment (t : ℝ) : ℝ := Real.log (blMoment μ h q t)

@[simp] theorem blMoment_zero : blMoment μ h q 0 = 1 := by
  simp [blMoment, blWeight]

omit [IsProbabilityMeasure μ] in
@[simp] theorem blMomentDeriv_zero : blMomentDeriv μ h q 0 = -(∫ x, h x ∂μ) := by
  simp [blMomentDeriv, blWeightDeriv, blWeight, integral_neg]

omit [IsProbabilityMeasure μ] in
theorem blMomentSecond_zero (hh2 : Integrable (fun x => h x ^ 2) μ) (hq : Integrable q μ) :
    blMomentSecond μ h q 0 = (∫ x, h x ^ 2 ∂μ) - ∫ x, q x ∂μ := by
  simp only [blMomentSecond, blWeightSecond, blWeight, neg_zero, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, sub_zero, Real.exp_zero, mul_one]
  exact integral_sub hh2 hq

variable {h q} {B : ℝ}

theorem hasDerivAt_blMoment (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blMoment μ h q) (blMomentDeriv μ h q t) t :=
  boundedKernel_hasDerivAt_integral blWeight blWeightDeriv continuous_blWeight
    continuous_blWeightDeriv hasDerivAt_blWeight hh hq hhB hqB ht

theorem hasDerivAt_blMomentDeriv (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blMomentDeriv μ h q) (blMomentSecond μ h q t) t :=
  boundedKernel_hasDerivAt_integral blWeightDeriv blWeightSecond continuous_blWeightDeriv
    continuous_blWeightSecond hasDerivAt_blWeightDeriv hh hq hhB hqB ht

theorem blMoment_pos (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : 0 < blMoment μ h q t :=
  integral_exp_pos (boundedKernel_integrable blWeight continuous_blWeight hh hq hhB hqB ht)

theorem hasDerivAt_blLogMoment (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (blLogMoment μ h q) (blMomentDeriv μ h q t / blMoment μ h q t) t :=
  (hasDerivAt_blMoment μ hh hq hhB hqB ht).log
    (blMoment_pos μ hh hq hhB hqB ⟨ht.1.le, ht.2.le⟩).ne'

theorem hasDerivAt_deriv_blLogMoment_zero (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B) :
    HasDerivAt (deriv (blLogMoment μ h q)) (variance μ h - ∫ x, q x ∂μ) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hhint : Integrable h μ := boundedKernel_integrable (fun _ a _ => a)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hh2int : Integrable (fun x => h x ^ 2) μ := boundedKernel_integrable (fun _ a _ => a ^ 2)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hqint : Integrable q μ := boundedKernel_integrable (fun _ _ b => b)
    (by fun_prop) hh hq hhB hqB (t := 0) ⟨by norm_num, by norm_num⟩
  have hd := (hasDerivAt_blMomentDeriv μ hh hq hhB hqB h0).div
    (hasDerivAt_blMoment μ hh hq hhB hqB h0) (by simp)
  have hratio : HasDerivAt (fun t => blMomentDeriv μ h q t / blMoment μ h q t)
      (variance μ h - ∫ x, q x ∂μ) 0 := by
    convert hd using 1
    rw [blMomentSecond_zero μ h q hh2int hqint, blMoment_zero, blMomentDeriv_zero,
      variance_eq_integral_sq_sub_sq μ hhint hh2int]
    ring
  apply hratio.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht
  exact (hasDerivAt_blLogMoment μ hh hq hhB hqB ht).deriv

theorem variance_le_integral_of_concave_blLogMoment
    (hh : Measurable h) (hq : Measurable q)
    (hhB : ∀ x, |h x| ≤ B) (hqB : ∀ x, |q x| ≤ B)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε) (blLogMoment μ h q)) :
    variance μ h ≤ ∫ x, q x ∂μ := by
  have hdiff : ∀ t ∈ Ioo (-ε) ε, DifferentiableAt ℝ (blLogMoment μ h q) t := by
    intro t ht
    exact (hasDerivAt_blLogMoment μ hh hq hhB hqB ⟨by linarith [ht.1], by linarith [ht.2]⟩).differentiableAt
  have hant := hc.antitoneOn_deriv hdiff
  have hnonpos := hant.derivWithin_nonpos (x := 0)
  have hd := (hasDerivAt_deriv_blLogMoment_zero μ hh hq hhB hqB).hasDerivWithinAt
    (s := Ioo (-ε) ε)
  rw [hd.derivWithin (isOpen_Ioo.uniqueDiffWithinAt ⟨by linarith, hε⟩)] at hnonpos
  linarith

end Moments

end LeanBlast.KLS

end

end OAI
