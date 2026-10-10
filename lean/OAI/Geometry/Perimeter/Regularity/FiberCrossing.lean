import OAI.Geometry.Perimeter.Regularity.GeoAlgebra

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace RPISingularHarnack

def fiberPrimitive (q : ℝ → ℝ) (l s : ℝ) : ℝ := ∫ t in l..s, q t

theorem fiberPrimitive_hasDerivAt {q : ℝ → ℝ} (hq : Continuous q) (l s : ℝ) :
    HasDerivAt (fiberPrimitive q l) (q s) s :=
  intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable _ _)
    hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

theorem fiberPrimitive_continuous {q : ℝ → ℝ} (hq : Continuous q) (l : ℝ) :
    Continuous (fiberPrimitive q l) :=
  continuous_iff_continuousAt.mpr (fun s ↦ (fiberPrimitive_hasDerivAt hq l s).continuousAt)

theorem fiber_crossing_identity {q : ℝ → ℝ} (hq : Continuous q) (l u : ℝ) :
    2 * (∫ s in l..u, (s-l)*q s) - (∫ s in l..u, q s)^2 =
      2 * ∫ s in l..u, q s * ((s-l)-fiberPrimitive q l s) := by
  have hF := fiberPrimitive_continuous hq l
  have hprod : (∫ s in l..u, q s*fiberPrimitive q l s + fiberPrimitive q l s*q s) =
      (fiberPrimitive q l u)^2 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub (a := l) (b := u)
      (fun s _ ↦ fiberPrimitive_hasDerivAt hq l s)
      (fun s _ ↦ fiberPrimitive_hasDerivAt hq l s)
      (hq.intervalIntegrable _ _) (hq.intervalIntegrable _ _)
    simpa only [fiberPrimitive,intervalIntegral.integral_same,mul_zero,sub_zero,pow_two] using h
  have hsq : 2*(∫ s in l..u, q s*fiberPrimitive q l s) = (∫ s in l..u, q s)^2 := by
    have he : (fun s ↦ q s*fiberPrimitive q l s + fiberPrimitive q l s*q s) =
        (fun s ↦ (2:ℝ)*(q s*fiberPrimitive q l s)) := by funext s; ring
    rw [he,intervalIntegral.integral_const_mul] at hprod
    exact hprod
  have he : (fun s ↦ q s * ((s-l)-fiberPrimitive q l s)) =
      (fun s ↦ (s-l)*q s-q s*fiberPrimitive q l s) := by funext s; ring
  rw [he]
  have hi₁ : IntervalIntegrable (fun s ↦ (s-l)*q s) volume l u :=
    ((continuous_id.sub continuous_const).mul hq).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun s ↦ q s*fiberPrimitive q l s) volume l u :=
    (hq.mul hF).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi₁ hi₂]
  linarith

theorem fiber_crossing_bound_of_order_defect {q : ℝ → ℝ} (hq : Continuous q)
    {l u D : ℝ} (hlu : l ≤ u) (hD : 0 ≤ D)
    (hb : ∀ s ∈ Icc l u, 0 ≤ q s ∧ q s ≤ 1)
    (horder : ∀ t ∈ Icc l u, ∀ s ∈ Icc t u, q s-q t ≤ D) :
    0 ≤ 2*(∫ s in l..u, (s-l)*q s)-(∫ s in l..u, q s)^2 ∧
    2*(∫ s in l..u, (s-l)*q s)-(∫ s in l..u, q s)^2 ≤
      2*(u-l)*(∫ s in l..u, q s*(1-q s))+2*(u-l)^2*D := by
  rw [fiber_crossing_identity hq l u]
  have hF := fiberPrimitive_continuous hq l
  have hi : IntervalIntegrable (fun s ↦ q s*((s-l)-fiberPrimitive q l s)) volume l u :=
    (hq.mul ((continuous_id.sub continuous_const).sub hF)).intervalIntegrable _ _
  have hlen (s : ℝ) : (s-l)-fiberPrimitive q l s = ∫ t in l..s, 1-q t := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hq.intervalIntegrable _ _)]
    simp [fiberPrimitive]
  have hpoint (s : ℝ) (hs : s ∈ Icc l u) :
      0 ≤ q s*((s-l)-fiberPrimitive q l s) ∧
      q s*((s-l)-fiberPrimitive q l s) ≤
        (u-l)*(q s*(1-q s))+(u-l)*D := by
    have hqs := hb s hs
    have hnon : 0 ≤ (s-l)-fiberPrimitive q l s := by
      rw [hlen]
      apply intervalIntegral.integral_nonneg hs.1
      intro t ht
      exact sub_nonneg.mpr (hb t ⟨ht.1,ht.2.trans hs.2⟩).2
    refine ⟨mul_nonneg hqs.1 hnon, ?_⟩
    have hbound : (s-l)-fiberPrimitive q l s ≤ (s-l)*(1-q s+D) := by
      rw [hlen]
      calc
        _ ≤ ∫ t in l..s, (1-q s+D) := by
          apply intervalIntegral.integral_mono_on hs.1
            ((continuous_const.sub hq).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
          intro t ht
          change 1-q t ≤ 1-q s+D
          have h := horder t ⟨ht.1,ht.2.trans hs.2⟩ s ⟨ht.2,hs.2⟩
          linarith
        _ = _ := by simp; ring
    have h₁ := mul_le_mul_of_nonneg_left hbound hqs.1
    have h₂ : (s-l)*(q s*(1-q s)) ≤ (u-l)*(q s*(1-q s)) := by
      exact mul_le_mul_of_nonneg_right (by linarith [hs.2]) (mul_nonneg hqs.1 (sub_nonneg.mpr hqs.2))
    have h₃ : (s-l)*q s*D ≤ (u-l)*D := by
      have hsq : (s-l)*q s ≤ u-l := by
        calc
          _ ≤ (s-l)*1 := mul_le_mul_of_nonneg_left hqs.2 (sub_nonneg.mpr hs.1)
          _ ≤ _ := by linarith [hs.2]
      exact mul_le_mul_of_nonneg_right hsq hD
    nlinarith
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hlu (fun s hs ↦ (hpoint s hs).1))
  · have h := intervalIntegral.integral_mono_on hlu hi
      ((continuous_const.mul (hq.mul (continuous_const.sub hq)) |>.add continuous_const).intervalIntegrable _ _)
      (fun s hs ↦ (hpoint s hs).2)
    change (∫ s in l..u, q s*((s-l)-fiberPrimitive q l s)) ≤
      ∫ s in l..u, (u-l)*(q s*(1-q s))+(u-l)*D at h
    have hi₁ : IntervalIntegrable (fun s ↦ (u-l)*(q s*(1-q s))) volume l u :=
      (continuous_const.mul (hq.mul (continuous_const.sub hq))).intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (fun _ : ℝ ↦ (u-l)*D) volume l u :=
      continuous_const.intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi₁ hi₂,intervalIntegral.integral_const_mul] at h
    simp only [intervalIntegral.integral_const,smul_eq_mul] at h
    nlinarith

theorem fiber_order_defect_of_positive_derivative {q : ℝ → ℝ}
    (hq : ContDiff ℝ 1 q) {l u t s : ℝ}
    (ht : t ∈ Icc l u) (hs : s ∈ Icc t u) :
    q s-q t ≤ ∫ r in l..u, max (deriv q r) 0 := by
  have hd : Continuous (deriv q) := hq.continuous_deriv (by simp)
  rw [← intervalIntegral.integral_deriv_eq_sub
    (fun x _ ↦ hq.differentiable (by simp) x) (hd.intervalIntegrable _ _)]
  calc
    _ ≤ ∫ r in t..s, max (deriv q r) 0 :=
      intervalIntegral.integral_mono hs.1 (hd.intervalIntegrable _ _)
        ((hd.max continuous_const).intervalIntegrable _ _) (fun _ ↦ le_max_left _ _)
    _ ≤ _ := intervalIntegral.integral_mono_interval ht.1 hs.1 hs.2
      (ae_of_all _ (fun _ ↦ le_max_right _ _)) ((hd.max continuous_const).intervalIntegrable _ _)

theorem fiber_crossing_bound {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {l u : ℝ} (hlu : l ≤ u) (hb : ∀ s ∈ Icc l u, 0 ≤ q s ∧ q s ≤ 1) :
    0 ≤ 2*(∫ s in l..u, (s-l)*q s)-(∫ s in l..u, q s)^2 ∧
    2*(∫ s in l..u, (s-l)*q s)-(∫ s in l..u, q s)^2 ≤
      2*(u-l)*(∫ s in l..u, q s*(1-q s))+
        2*(u-l)^2*(∫ s in l..u, max (deriv q s) 0) := by
  apply fiber_crossing_bound_of_order_defect hq.continuous hlu
    (intervalIntegral.integral_nonneg hlu (fun _ _ ↦ le_max_right _ _)) hb
  exact fun _ ht _ hs ↦ fiber_order_defect_of_positive_derivative hq ht hs

theorem fiber_flux_height_identity {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {l u : ℝ} (hl : q l = 1) (hu : q u = 0) :
    (∫ s in l..u, s^2 * (-deriv q s)) - (l+∫ s in l..u, q s)^2 =
      2*(∫ s in l..u, (s-l)*q s)-(∫ s in l..u, q s)^2 := by
  have hd : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have hpow (s : ℝ) : HasDerivAt (fun t : ℝ ↦ t^2) (2*s) s := by
    simpa using (hasDerivAt_pow 2 s)
  have hprod := intervalIntegral.integral_deriv_mul_eq_sub (a := l) (b := u)
    (fun s _ ↦ hpow s) (fun s _ ↦ (hq.differentiable (by simp) s).hasDerivAt)
    ((continuous_const.mul continuous_id).intervalIntegrable l u)
    (hd.intervalIntegrable l u)
  have hi₁ : IntervalIntegrable (fun s ↦ 2*s*q s) volume l u :=
    ((continuous_const.mul continuous_id).mul hq.continuous).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun s ↦ s^2*deriv q s) volume l u :=
    ((continuous_id.pow 2).mul hd).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi₁ hi₂,hl,hu,mul_zero,mul_one,zero_sub] at hprod
  have he₁ : (∫ s in l..u, s^2*(-deriv q s)) = -(∫ s in l..u, s^2*deriv q s) := by
    simp_rw [mul_neg]
    exact intervalIntegral.integral_neg
  have he₂ : (∫ s in l..u, (s-l)*q s) =
      (∫ s in l..u, s*q s)-l*(∫ s in l..u, q s) := by
    simp_rw [sub_mul]
    have hi₁ : IntervalIntegrable (fun s ↦ s*q s) volume l u :=
      (continuous_id.mul hq.continuous).intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (fun s ↦ l*q s) volume l u :=
      (continuous_const.mul hq.continuous).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul]
  have he₃ : (∫ s in l..u, 2*s*q s) = 2*(∫ s in l..u, s*q s) := by
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
  rw [he₃] at hprod
  rw [he₁,he₂]
  nlinarith

theorem fiber_flux_height_defect {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {l u : ℝ} (hlu : l ≤ u) (hl : q l = 1) (hu : q u = 0)
    (hb : ∀ s ∈ Icc l u, 0 ≤ q s ∧ q s ≤ 1) :
    0 ≤ (∫ s in l..u, s^2*(-deriv q s))-(l+∫ s in l..u, q s)^2 ∧
    (∫ s in l..u, s^2*(-deriv q s))-(l+∫ s in l..u, q s)^2 ≤
      2*(u-l)*(∫ s in l..u, q s*(1-q s))+
        2*(u-l)^2*(∫ s in l..u, max (deriv q s) 0) := by
  rw [fiber_flux_height_identity hq hl hu]
  exact fiber_crossing_bound hq hlu hb

end RPISingularHarnack

end

end OAI
