import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set MeasureTheory
open scoped Topology

lemma duhamel_signed_error {E D : ℝ → ℝ} {T M κ a : ℝ}
    (hT : 0 ≤ T) (hM : 0 < M)
    (hEi : IntervalIntegrable E volume 0 T)
    (hlo : ∀ s ∈ Icc 0 T, E 0 ≤ M*E s)
    (hhi : ∀ s ∈ Icc 0 T, E s ≤ M*E T)
    (hduh : 2*(κ*(∫ s in 0..T,E s)-a*(∫ s in 0..T,D s)) ≤ E T-E 0) :
    (1+2*max κ 0*T/M)*E 0 ≤
      (1+2*max (-κ) 0*T*M)*E T+2*a*(∫ s in 0..T,D s) := by
  have hl : T*(E 0/M) ≤ ∫ s in 0..T,E s := by
    have H := intervalIntegral.integral_mono_on hT intervalIntegrable_const hEi
      (fun s hs => (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hlo s hs))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using H
  have hh : (∫ s in 0..T,E s) ≤ T*(M*E T) := by
    have H := intervalIntegral.integral_mono_on hT hEi intervalIntegrable_const hhi
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using H
  have hk : max κ 0-max (-κ) 0 = κ := by
    rcases le_total 0 κ with h|h
    · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
    · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]; ring
  have HL := mul_le_mul_of_nonneg_left hl (le_max_right κ 0)
  have HH := mul_le_mul_of_nonneg_left hh (le_max_right (-κ) 0)
  have key' : max κ 0*T/M*E 0-max (-κ) 0*T*M*E T ≤ κ*(∫ s in 0..T,E s) := by
    calc
      _ = max κ 0*(T*(E 0/M))-max (-κ) 0*(T*(M*E T)) := by ring
      _ ≤ max κ 0*(∫ s in 0..T,E s)-max (-κ) 0*(∫ s in 0..T,E s) := sub_le_sub HL HH
      _ = κ*(∫ s in 0..T,E s) := by rw [← sub_mul,hk]
  simp only [div_eq_mul_inv] at key' ⊢
  nlinarith only [hduh,key']

lemma duhamel_signed_error_ratio {E D : ℝ → ℝ} {T M κ a : ℝ}
    (hT : 0 ≤ T) (hM : 0 < M)
    (hEi : IntervalIntegrable E volume 0 T)
    (hlo : ∀ s ∈ Icc 0 T, E 0 ≤ M*E s)
    (hhi : ∀ s ∈ Icc 0 T, E s ≤ M*E T)
    (hduh : 2*(κ*(∫ s in 0..T,E s)-a*(∫ s in 0..T,D s)) ≤ E T-E 0) :
    ((1+2*max κ 0*T/M)/(1+2*max (-κ) 0*T*M))*E 0 ≤
      E T+(2*a/(1+2*max (-κ) 0*T*M))*(∫ s in 0..T,D s) := by
  have hp : 0 < 1+2*max (-κ) 0*T*M := by positivity
  have H := duhamel_signed_error hT hM hEi hlo hhi hduh
  have H' := div_le_div_of_nonneg_right H hp.le
  calc
    _ = ((1+2*max κ 0*T/M)*E 0)/(1+2*max (-κ) 0*T*M) := by ring
    _ ≤ ((1+2*max (-κ) 0*T*M)*E T+2*a*(∫ s in 0..T,D s))/(1+2*max (-κ) 0*T*M) := H'
    _ = _ := by rw [add_div,mul_div_cancel_left₀ _ hp.ne']; ring

end WeakHessian

end
end

end OAI
