import Mathlib
import OAI.Analysis.Conductivity.Sobolev.IntervalTraceEnergy

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma smooth_interval_oscillation {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b x y : ℝ} (hab : a ≤ b)
    (hx : x∈Icc a b) (hy : y∈Icc a b) :
    (q x-q y)^2 ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) := by
  have hd := hq.continuous_deriv (by simp)
  have hD : 0 ≤ ∫ t in a..b, (deriv q t)^2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have haux (u v : ℝ) (hu : u∈Icc a b) (hv : v∈Icc a b) (huv : u ≤ v) :
      (q v-q u)^2 ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) := by
    have h := smooth_interval_poincare_point hq huv
    have hi : (∫ t in u..v, (deriv q t)^2) ≤ ∫ t in a..b, (deriv q t)^2 :=
      intervalIntegral.integral_mono_interval hu.1 huv hv.2
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hd.pow 2).intervalIntegrable _ _)
    calc
      _ ≤ (v-u)*(∫ t in u..v, (deriv q t)^2) := h
      _ ≤ (v-u)*(∫ t in a..b, (deriv q t)^2) := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr huv)
      _ ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) :=
        mul_le_mul_of_nonneg_right (by linarith [hu.1,hv.2]) hD
  rcases le_total x y with hxy|hyx
  · have he : (q x-q y)^2=(q y-q x)^2 := by ring
    rw [he]; exact haux x y hx hy hxy
  · exact haux y x hy hx hyx

theorem smooth_interval_mean_point {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b x : ℝ} (hab : a<b) (hx : x∈Icc a b) :
    (q x-(∫ t in a..b, q t)/(b-a))^2 ≤ (b-a)*(∫ t in a..b, (deriv q t)^2) := by
  let L := b-a
  let D := ∫ t in a..b, (deriv q t)^2
  let M := (∫ t in a..b, q t)/L
  have hL : 0<L := sub_pos.mpr hab
  have hcs := interval_integral_sq_le hab.le (continuous_const.sub hq.continuous : Continuous (fun t => q x-q t))
  have hi : (∫ t in a..b, (q x-q t)^2) ≤ L^2*D := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (f := fun t => (q x-q t)^2)
      (g := fun _ => L*D) hab.le
      ((continuous_const.sub hq.continuous).pow 2 |>.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => smooth_interval_oscillation hq hab.le hx ht)
    rw [intervalIntegral.integral_const,smul_eq_mul] at hh
    dsimp [L] at hh ⊢
    nlinarith
  change (∫ t in a..b, q x-q t)^2 ≤ (b-a)*(∫ t in a..b, (q x-q t)^2) at hcs
  rw [intervalIntegral.integral_sub (f := fun _ => q x) (g := q)
    (continuous_const.intervalIntegrable a b) (hq.continuous.intervalIntegrable a b),
    intervalIntegral.integral_const,smul_eq_mul] at hcs
  have hM : L*M=∫ t in a..b, q t := mul_div_cancel₀ _ hL.ne'
  change (q x-M)^2 ≤ L*D
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp
  have hc : (L*q x-L*M)^2 ≤ L*(L^2*D) := by
    rw [hM]
    exact hcs.trans (mul_le_mul_of_nonneg_left hi hL.le)
  nlinarith

lemma smooth_interval_mean_poincare {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {a b : ℝ} (hab : a<b) :
    (∫ x in a..b, (q x-(∫ t in a..b, q t)/(b-a))^2) ≤
      (b-a)^2*(∫ t in a..b, (deriv q t)^2) := by
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun x => (q x-(∫ t in a..b, q t)/(b-a))^2)
    (g := fun _ => (b-a)*(∫ t in a..b, (deriv q t)^2)) hab.le
    ((hq.continuous.sub continuous_const).pow 2 |>.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b)
    (fun x hx => smooth_interval_mean_point hq hab hx)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hi
  nlinarith

end ScalarConductivity

end

end OAI
