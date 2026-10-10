import OAI.Geometry.RCD.Metric.CommonDensityMinorization

namespace OAI

/-! # Common minorization of normalized positive kernel rows

Uniform lower and upper kernel bounds give a strict loss in the
oscillation of weighted means, independently of the positive base weight.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates

private theorem normalized_weight_lower {m M S Z k r : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hS : 0 < S) (hZ : 0 < Z)
    (hZS : Z ≤ M*S) (hk : m ≤ k) (hr : 0 ≤ r) :
    (m/M)*(r/S) ≤ k*r/Z := by
  calc
    _ = m*r/(M*S) := by ring
    _ ≤ k*r/(M*S) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hk hr) (mul_nonneg hM.le hS.le)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (hm.le.trans hk) hr) hZ hZS

variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

theorem normalized_positive_weights_difference {r k v f : Y → ℝ} {m M a b : ℝ}
    (hr : Integrable r μ) (hfr : Integrable (fun x => f x*r x) μ)
    (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x) (hS : 0 < ∫ x, r x ∂μ)
    (hk : Measurable k) (hv : Measurable v) (hm : 0 < m)
    (hkb : ∀ x, m ≤ k x ∧ k x ≤ M) (hvb : ∀ x, m ≤ v x ∧ v x ≤ M)
    (hf : ∀ᵐ x ∂μ, a ≤ f x ∧ f x ≤ b) :
    |(∫ x, f x*(k x*r x) ∂μ)/(∫ x, k x*r x ∂μ)-
      (∫ x, f x*(v x*r x) ∂μ)/(∫ x, v x*r x ∂μ)| ≤ (1-m/M)*(b-a) := by
  have hkn : ∀ᵐ x ∂μ, ‖k x‖ ≤ M := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hm.le.trans (hkb x).1)]
    exact (hkb x).2
  have hvn : ∀ᵐ x ∂μ, ‖v x‖ ≤ M := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hm.le.trans (hvb x).1)]
    exact (hvb x).2
  have hkr : Integrable (fun x => k x*r x) μ := hr.bdd_mul hk.aestronglyMeasurable hkn
  have hvr : Integrable (fun x => v x*r x) μ := hr.bdd_mul hv.aestronglyMeasurable hvn
  have hfkr : Integrable (fun x => f x*(k x*r x)) μ := by
    convert hfr.bdd_mul hk.aestronglyMeasurable hkn using 1
    funext x
    change f x * (k x * r x) = k x * (f x * r x)
    ring
  have hfvr : Integrable (fun x => f x*(v x*r x)) μ := by
    convert hfr.bdd_mul hv.aestronglyMeasurable hvn using 1
    funext x
    change f x * (v x * r x) = v x * (f x * r x)
    ring
  let S := ∫ x, r x ∂μ
  let Zk := ∫ x, k x*r x ∂μ
  let Zv := ∫ x, v x*r x ∂μ
  have hZk : m*S ≤ Zk ∧ Zk ≤ M*S := by
    constructor
    · simpa only [integral_const_mul] using integral_mono_ae (hr.const_mul m) hkr
        (hr0.mono fun x hx => mul_le_mul_of_nonneg_right (hkb x).1 hx)
    · simpa only [integral_const_mul] using integral_mono_ae hkr (hr.const_mul M)
        (hr0.mono fun x hx => mul_le_mul_of_nonneg_right (hkb x).2 hx)
  have hZv : m*S ≤ Zv ∧ Zv ≤ M*S := by
    constructor
    · simpa only [integral_const_mul] using integral_mono_ae (hr.const_mul m) hvr
        (hr0.mono fun x hx => mul_le_mul_of_nonneg_right (hvb x).1 hx)
    · simpa only [integral_const_mul] using integral_mono_ae hvr (hr.const_mul M)
        (hr0.mono fun x hx => mul_le_mul_of_nonneg_right (hvb x).2 hx)
  have hZk0 : 0 < Zk := (mul_pos hm hS).trans_le hZk.1
  have hZv0 : 0 < Zv := (mul_pos hm hS).trans_le hZv.1
  have hM : 0 < M := by
    have hh : 0 < M*S := hZk0.trans_le hZk.2
    exact (mul_pos_iff_of_pos_right hS).mp hh
  let w0 := fun x => r x/S
  let wk := fun x => k x*r x/Zk
  let wv := fun x => v x*r x/Zv
  have hw0 : Integrable w0 μ := hr.div_const S
  have hwk : Integrable wk μ := hkr.div_const Zk
  have hwv : Integrable wv μ := hvr.div_const Zv
  have hfw0 : Integrable (fun x => f x*w0 x) μ := by
    simpa only [w0,← mul_div_assoc] using hfr.div_const S
  have hfwk : Integrable (fun x => f x*wk x) μ := by
    simpa only [wk,← mul_div_assoc] using hfkr.div_const Zk
  have hfwv : Integrable (fun x => f x*wv x) μ := by
    simpa only [wv,← mul_div_assoc] using hfvr.div_const Zv
  have hw01 : (∫ x, w0 x ∂μ)=1 := by rw [integral_div]; exact div_self hS.ne'
  have hwk1 : (∫ x, wk x ∂μ)=1 := by rw [integral_div]; exact div_self hZk0.ne'
  have hwv1 : (∫ x, wv x ∂μ)=1 := by rw [integral_div]; exact div_self hZv0.ne'
  have hminK : ∀ᵐ x ∂μ, (m/M)*w0 x ≤ wk x := hr0.mono fun x hx =>
    normalized_weight_lower hm hM hS hZk0 hZk.2 (hkb x).1 hx
  have hminV : ∀ᵐ x ∂μ, (m/M)*w0 x ≤ wv x := hr0.mono fun x hx =>
    normalized_weight_lower hm hM hS hZv0 hZv.2 (hvb x).1 hx
  have hh := common_density_mean_difference μ hw0 hwk hwv hfw0 hfwk hfwv
    hw01 hwk1 hwv1 hminK hminV hf
  simpa only [wk,wv,← mul_div_assoc,integral_div] using hh

end RegularPointCoordinates

end

end OAI
