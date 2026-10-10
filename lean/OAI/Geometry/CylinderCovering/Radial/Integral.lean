import Mathlib

namespace OAI

open Set MeasureTheory

noncomputable section

namespace CylinderCovering.RadialIntegral

theorem transverse_integral_bound {lam : ℝ → ℝ} {M c t : ℝ}
    (_hM : 0 ≤ M) (hlam : ∀ x ∈ uIcc c t, |lam x| ≤ M) :
    |∫ x in c..t, lam x * (x - t)| ≤ M * (t - c) ^ 2 / 2 := by
  by_cases hct : c ≤ t
  · have hbound : ∀ᵐ x : ℝ, x ∈ Ioc c t →
        ‖lam x * (x - t)‖ ≤ M * (t - x) := by
      filter_upwards [] with x hx
      have hxlam := hlam x (by simpa [uIcc_of_le hct] using
        (show x ∈ Icc c t from ⟨hx.1.le, hx.2⟩))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (sub_nonpos.mpr hx.2)]
      calc
        |lam x| * -(x - t) ≤ M * -(x - t) :=
          mul_le_mul_of_nonneg_right hxlam (by linarith [hx.2])
        _ = M * (t - x) := by ring
    have hi : IntervalIntegrable (fun x : ℝ => M * (t - x)) volume c t :=
      (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
    have hb := intervalIntegral.norm_integral_le_of_norm_le hct hbound hi
    have heval : (∫ x in c..t, M * (t - x)) = M * (t - c) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun _ : ℝ => t) (g := fun x : ℝ => x)
          intervalIntegrable_const (continuous_id.intervalIntegrable c t)]
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      ring
    simpa only [Real.norm_eq_abs, heval] using hb
  · have htc : t ≤ c := le_of_not_ge hct
    have hbound : ∀ᵐ x : ℝ, x ∈ Ioc t c →
        ‖lam x * (x - t)‖ ≤ M * (x - t) := by
      filter_upwards [] with x hx
      have hxlam := hlam x (by simpa [uIcc_of_ge htc] using
        (show x ∈ Icc t c from ⟨hx.1.le, hx.2⟩))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      exact mul_le_mul_of_nonneg_right hxlam (sub_nonneg.mpr hx.1.le)
    have hi : IntervalIntegrable (fun x : ℝ => M * (x - t)) volume t c :=
      (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
    have hb := intervalIntegral.norm_integral_le_of_norm_le htc hbound hi
    have heval : (∫ x in t..c, M * (x - t)) = M * (t - c) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => t)
          (continuous_id.intervalIntegrable t c) intervalIntegrable_const]
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      ring
    rw [intervalIntegral.integral_symm, abs_neg]
    simpa only [Real.norm_eq_abs, heval] using hb

theorem radial_integral_bound {lam : ℝ → ℝ} {M c t : ℝ}
    (hlam : ∀ x ∈ uIcc c t, |lam x| ≤ M) :
    |∫ x in c..t, lam x| ≤ M * |t - c| := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := c) (b := t) (C := M) (f := lam) (fun x hx => by
      simpa only [Real.norm_eq_abs] using hlam x (uIoc_subset_uIcc hx))
  simpa only [Real.norm_eq_abs, mul_comm] using hb

theorem integral_eq_sub_of_within_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {a b c t : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ x in c..t, f' x) = f t - f c := by
  have forward : ∀ c t : ℝ, c ∈ Icc a b → t ∈ Icc a b → c ≤ t →
      (∫ x in c..t, f' x) = f t - f c := by
    intro c t hc ht hct
    have hsub : Icc c t ⊆ Icc a b := fun x hx =>
      ⟨hc.1.trans hx.1, hx.2.trans ht.2⟩
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hct (hf.mono hsub)
    · intro x hx
      have hax : a < x := hc.1.trans_lt hx.1
      have hxb : x < b := hx.2.trans_le ht.2
      exact (hderiv x ⟨hax.le, hxb.le⟩).hasDerivAt (Icc_mem_nhds hax hxb)
    · exact ContinuousOn.intervalIntegrable_of_Icc hct (hf'.mono hsub)
  by_cases hct : c ≤ t
  · exact forward c t hc ht hct
  · rw [intervalIntegral.integral_symm, forward t c ht hc (le_of_not_ge hct)]
    abel

theorem integral_footprint {lam : ℝ → ℝ} {M L d c t m rho R s : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hlam : ∀ x ∈ uIcc c t, |lam x| ≤ M)
    (htc : |t - c| ≤ d) (htm : |t - m| ≤ d / 2)
    (hs : |s| ≤ L) (hrho : 0 ≤ rho) (hR : rho ≤ R) :
    let u := rho + s * (∫ x in c..t, lam x);
    let v := t * u + s * (∫ x in c..t, lam x * (x - t));
    -(L * M) * d ≤ u ∧ u ≤ R + (L * M) * d ∧
      |v - m * u| ≤ d / 2 * |u| + (L * M / 2) * d ^ 2 := by
  dsimp only
  have hI : |∫ x in c..t, lam x| ≤ M * d :=
    (radial_integral_bound hlam).trans (mul_le_mul_of_nonneg_left htc hM)
  have hsq : (t - c) ^ 2 ≤ d ^ 2 := by
    have := sq_le_sq₀ (abs_nonneg (t - c)) hd |>.mpr htc
    simpa only [sq_abs] using this
  have hJ : |∫ x in c..t, lam x * (x - t)| ≤ M * d ^ 2 / 2 :=
    (transverse_integral_bound hM hlam).trans (by nlinarith [mul_le_mul_of_nonneg_left hsq hM])
  have hrad : |s * (∫ x in c..t, lam x)| ≤ L * M * d := by
    rw [abs_mul]
    calc
      |s| * |∫ x in c..t, lam x| ≤ L * (M * d) :=
        mul_le_mul hs hI (abs_nonneg _) hL
      _ = L * M * d := by ring
  have htrans : |s * (∫ x in c..t, lam x * (x - t))| ≤
      (L * M / 2) * d ^ 2 := by
    rw [abs_mul]
    calc
      |s| * |∫ x in c..t, lam x * (x - t)| ≤ L * (M * d ^ 2 / 2) :=
        mul_le_mul hs hJ (abs_nonneg _) hL
      _ = (L * M / 2) * d ^ 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · have := (abs_le.mp hrad).1
    linarith
  · have := (abs_le.mp hrad).2
    linarith
  · rw [show t * (rho + s * (∫ x in c..t, lam x)) +
        s * (∫ x in c..t, lam x * (x - t)) -
        m * (rho + s * (∫ x in c..t, lam x)) =
        (t - m) * (rho + s * (∫ x in c..t, lam x)) +
        s * (∫ x in c..t, lam x * (x - t)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right htm (abs_nonneg _)) htrans

theorem aligned_increment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ → E} {lam : ℝ → ℝ} {a b c t : ℝ} {p q : E}
    (hw : ContinuousOn w (Icc a b)) (hlam : ContinuousOn lam (Icc a b))
    (hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt w (lam x • (p + x • q)) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    w t - w c = (∫ x in c..t, lam x) • (p + t • q) +
      (∫ x in c..t, lam x * (x - t)) • q := by
  have hsub : uIcc c t ⊆ Icc a b := uIcc_subset_Icc hc ht
  have hvel : ContinuousOn (fun x => lam x • (p + x • q)) (Icc a b) :=
    hlam.smul (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  rw [← integral_eq_sub_of_within_deriv hw hvel hderiv hc ht]
  have hpoint : (fun x => lam x • (p + x • q)) =
      (fun x => lam x • (p + t • q) + (lam x * (x - t)) • q) := by
    funext x
    module
  rw [hpoint]
  have hrad : IntervalIntegrable (fun x => lam x • (p + t • q)) volume c t :=
    ((hlam.mono hsub).smul continuousOn_const).intervalIntegrable
  have htrans : IntervalIntegrable (fun x => (lam x * (x - t)) • q) volume c t :=
    (((hlam.mono hsub).mul (continuous_id.sub continuous_const).continuousOn).smul
      continuousOn_const).intervalIntegrable
  rw [intervalIntegral.integral_add hrad htrans]
  simp only [intervalIntegral.integral_smul_const]

theorem aligned_frozen_intercept
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ → E} {lam : ℝ → ℝ} {a b c t rho s : ℝ} {p q p0 : E}
    (hw : ContinuousOn w (Icc a b)) (hlam : ContinuousOn lam (Icc a b))
    (hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt w (lam x • (p + x • q)) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    let u := rho + s * (∫ x in c..t, lam x);
    let v := t * u + s * (∫ x in c..t, lam x * (x - t));
    p0 + rho • (p + t • q) + s • (w t - w c) = p0 + u • p + v • q := by
  dsimp only
  rw [aligned_increment hw hlam hderiv hc ht]
  module

theorem aligned_footprint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ → E} {lam : ℝ → ℝ}
    {a b c t m rho R s M L d : ℝ} {p q p0 : E}
    (hw : ContinuousOn w (Icc a b)) (hlam : ContinuousOn lam (Icc a b))
    (hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt w (lam x • (p + x • q)) (Icc a b) x)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hbound : ∀ x ∈ Icc a b, |lam x| ≤ M)
    (htc : |t - c| ≤ d) (htm : |t - m| ≤ d / 2)
    (hs : |s| ≤ L) (hrho : 0 ≤ rho) (hR : rho ≤ R) :
    ∃ u v : ℝ,
      p0 + rho • (p + t • q) + s • (w t - w c) = p0 + u • p + v • q ∧
      -(L * M) * d ≤ u ∧ u ≤ R + (L * M) * d ∧
      |v - m * u| ≤ d / 2 * |u| + (L * M / 2) * d ^ 2 := by
  let u := rho + s * (∫ x in c..t, lam x)
  let v := t * u + s * (∫ x in c..t, lam x * (x - t))
  refine ⟨u, v, aligned_frozen_intercept hw hlam hderiv hc ht, ?_⟩
  exact integral_footprint hM hL hd
    (fun x hx => hbound x (uIcc_subset_Icc hc ht hx)) htc htm hs hrho hR

end CylinderCovering.RadialIntegral

end

end OAI
