import Mathlib

namespace OAI

open Set MeasureTheory

noncomputable section

namespace CylinderCovering.RadialIntercept

theorem integral_bound {f : ℝ → ℝ} {c t M : ℝ}
    (hf : ∀ x ∈ uIcc c t, |f x| ≤ M) :
    |∫ x in c..t, f x| ≤ M * |t - c| := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  simpa only [Real.norm_eq_abs] using hf x (Ioc_subset_Icc_self hx)

theorem transverse_bound_of_le {f : ℝ → ℝ} {c t M : ℝ}
    (hct : c ≤ t) (hf : ∀ x ∈ Icc c t, |f x| ≤ M) :
    |∫ x in c..t, f x * (x - t)| ≤ M * (t - c) ^ 2 / 2 := by
  have hbound : IntervalIntegrable (fun x : ℝ => M * (t - x)) volume c t :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le hct
    (f := fun x : ℝ => f x * (x - t))
    (g := fun x : ℝ => M * (t - x))
    (Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (sub_nonpos.mpr hx.2)]
      have := mul_le_mul_of_nonneg_right (hf x ⟨le_of_lt hx.1, hx.2⟩)
        (sub_nonneg.mpr hx.2)
      nlinarith)) hbound
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (show IntervalIntegrable (fun _ : ℝ => t) volume c t from continuous_const.intervalIntegrable _ _)
      (show IntervalIntegrable (fun x : ℝ => x) volume c t from continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id] at h
  simp only [Real.norm_eq_abs, smul_eq_mul] at h
  convert h using 1
  ring

theorem transverse_bound_of_ge {f : ℝ → ℝ} {c t M : ℝ}
    (htc : t ≤ c) (hf : ∀ x ∈ Icc t c, |f x| ≤ M) :
    |∫ x in c..t, f x * (x - t)| ≤ M * (t - c) ^ 2 / 2 := by
  have hbound : IntervalIntegrable (fun x : ℝ => M * (x - t)) volume t c :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le htc
    (f := fun x : ℝ => f x * (x - t))
    (g := fun x : ℝ => M * (x - t))
    (Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr (le_of_lt hx.1))]
      exact mul_le_mul_of_nonneg_right (hf x ⟨le_of_lt hx.1, hx.2⟩)
        (sub_nonneg.mpr (le_of_lt hx.1)))) hbound
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (show IntervalIntegrable (fun x : ℝ => x) volume t c from continuous_id.intervalIntegrable _ _)
      (show IntervalIntegrable (fun _ : ℝ => t) volume t c from continuous_const.intervalIntegrable _ _),
    integral_id, intervalIntegral.integral_const] at h
  rw [intervalIntegral.integral_symm t c, abs_neg]
  simp only [Real.norm_eq_abs, smul_eq_mul] at h
  convert h using 1
  ring

theorem transverse_bound {f : ℝ → ℝ} {c t M : ℝ}
    (hf : ∀ x ∈ uIcc c t, |f x| ≤ M) :
    |∫ x in c..t, f x * (x - t)| ≤ M * (t - c) ^ 2 / 2 := by
  rcases le_total c t with hct | htc
  · exact transverse_bound_of_le hct (by simpa only [uIcc_of_le hct] using hf)
  · exact transverse_bound_of_ge htc (by simpa only [uIcc_of_ge htc] using hf)

theorem integral_bounds_on_interval {f : ℝ → ℝ} {a b c t M : ℝ}
    (hM : 0 ≤ M) (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    |∫ x in c..t, f x| ≤ M * (b - a) ∧
    |∫ x in c..t, f x * (x - t)| ≤ M * (b - a) ^ 2 / 2 := by
  have hsub : uIcc c t ⊆ Icc a b := uIcc_subset_Icc hc ht
  have hdist : |t - c| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, ht.1, ht.2]
  constructor
  · exact (integral_bound (fun x hx => hf x (hsub hx))).trans
      (mul_le_mul_of_nonneg_left hdist hM)
  · have hsq : (t - c) ^ 2 ≤ (b - a) ^ 2 := by
      nlinarith [sq_abs (t - c), abs_nonneg (t - c)]
    exact (transverse_bound (fun x hx => hf x (hsub hx))).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hM) (by norm_num))

theorem intercept_footprint {f : ℝ → ℝ} {a b c t M L R ρ s u v : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (hs : |s| ≤ L)
    (hρ : 0 ≤ ρ ∧ ρ ≤ R)
    (hu : u = ρ + s * ∫ x in c..t, f x)
    (hv : v - t * u = s * ∫ x in c..t, f x * (x - t)) :
    -(L * M) * (b - a) ≤ u ∧ u ≤ R + (L * M) * (b - a) ∧
      |v - ((a + b) / 2) * u| ≤
        (b - a) / 2 * |u| + (L * M / 2) * (b - a) ^ 2 := by
  obtain ⟨hI, hJ⟩ := integral_bounds_on_interval hM hc ht hf
  have hrad : |s * ∫ x in c..t, f x| ≤ L * (M * (b - a)) := by
    rw [abs_mul]
    exact mul_le_mul hs hI (abs_nonneg _) hL
  have htrans : |v - t * u| ≤ L * (M * (b - a) ^ 2 / 2) := by
    rw [hv, abs_mul]
    exact mul_le_mul hs hJ (abs_nonneg _) hL
  have hmid : |t - (a + b) / 2| ≤ (b - a) / 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hwidth : |(t - (a + b) / 2) * u| ≤ (b - a) / 2 * |u| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hmid (abs_nonneg _)
  rcases abs_le.mp hrad with ⟨hradlo, hradhi⟩
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hρ.1]
  · nlinarith [hρ.2]
  · calc
      |v - ((a + b) / 2) * u| =
          |(v - t * u) + (t - (a + b) / 2) * u| := by congr 1; ring
      _ ≤ |v - t * u| + |(t - (a + b) / 2) * u| := abs_add_le _ _
      _ ≤ L * (M * (b - a) ^ 2 / 2) + (b - a) / 2 * |u| :=
        add_le_add htrans hwidth
      _ = (b - a) / 2 * |u| + (L * M / 2) * (b - a) ^ 2 := by ring

end CylinderCovering.RadialIntercept

end

end OAI
