import OAI.NumberTheory.Ostmann.Dirichlet.LocalZeroCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open scoped BigOperators

def contourJensenCenter (T : ℝ) : ℝ := 100 * (T + 4)^2

lemma contourJensenCenter_ge {T : ℝ} (hT : 1 ≤ T) : 100 ≤ contourJensenCenter T := by
  unfold contourJensenCenter
  nlinarith [sq_nonneg (T + 3)]

lemma contour_zero_mem_disk {T : ℝ} (hT : 1 ≤ T) {rho : ℂ}
    (hre : 3/20 ≤ rho.re) (hre1 : rho.re ≤ 1) (him : |rho.im| ≤ T+4) :
    rho ∈ Metric.closedBall (contourJensenCenter T : ℂ) (contourJensenCenter T - 1/10) := by
  have hc := contourJensenCenter_ge hT
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hn : ‖rho - (contourJensenCenter T : ℂ)‖^2 =
      (rho.re-contourJensenCenter T)^2 + rho.im^2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hresq : rho.re^2 ≤ 1 := by nlinarith
  have himsq : rho.im^2 ≤ (T+4)^2 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp him
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hre (show 0 ≤ contourJensenCenter T by linarith)
  have hceq : contourJensenCenter T = 100*(T+4)^2 := rfl
  nlinarith [norm_nonneg (rho - (contourJensenCenter T : ℂ))]

lemma norm_LFunction_contour_disk {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {T : ℝ} (hT : 1 ≤ T)
    {z : ℂ} (hz : z ∈ Metric.closedBall (contourJensenCenter T : ℂ)
      (contourJensenCenter T - 1/20)) :
    ‖chi.LFunction z‖ ≤ 40 * q * contourJensenCenter T := by
  have hc := contourJensenCenter_ge hT
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre : 1/20 ≤ z.re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm
      (z-(contourJensenCenter T:ℂ))).trans hz)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    linarith
  have hnorm : ‖z‖ ≤ 2*contourJensenCenter T := by
    have h := norm_add_le (z-(contourJensenCenter T:ℂ)) (contourJensenCenter T:ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h
    linarith
  have hL := norm_LFunction_le_partial_sum_bound chi hchi (by linarith : 0 < z.re)
  apply hL.trans
  apply (div_le_iff₀ (by linarith : 0 < z.re)).mpr
  have h1 := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ (q:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hre
    (show 0 ≤ 40*(q:ℝ)*contourJensenCenter T by positivity)
  nlinarith

lemma contour_jensen_log_lower {T : ℝ} (hT : 1 ≤ T) :
    1/(20*contourJensenCenter T) ≤
      Real.log ((contourJensenCenter T-1/20)/(contourJensenCenter T-1/10)) := by
  have hc := contourJensenCenter_ge hT
  have hr : 0 < contourJensenCenter T-1/10 := by linarith
  have hR : 0 < contourJensenCenter T-1/20 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hR hr)
  have he : 1-((contourJensenCenter T-1/20)/(contourJensenCenter T-1/10))⁻¹ =
      1/(20*(contourJensenCenter T-1/20)) := by
    rw [inv_div, one_sub_div hR.ne']
    rw [show (contourJensenCenter T-1/20)-(contourJensenCenter T-1/10) = (1:ℝ)/20 by ring, div_div]
  rw [he] at h
  exact (one_div_le_one_div_of_le (by positivity)
    (show 20*(contourJensenCenter T-1/20) ≤ 20*contourJensenCenter T by linarith)).trans h

theorem contour_zero_multiplicity_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {T : ℝ} (hT : 1 ≤ T)
    (S : Finset ℂ) (hS : ∀ rho ∈ S, 3/20 ≤ rho.re ∧ rho.re ≤ 1 ∧ |rho.im| ≤ T+4) :
    (∑ rho ∈ S, (zeroMultiplicity chi rho : ℝ)) ≤
      8000000 * absoluteZetaTwo * q * (T+4)^4 := by
  have hc := contourJensenCenter_ge hT
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hZ := one_le_absoluteZetaTwo
  have hne := LFunction_ne_zero_right chi
    (s := (contourJensenCenter T:ℂ)) (by simpa using (show 1 < contourJensenCenter T by linarith))
  have hn : 0 < ‖chi.LFunction (contourJensenCenter T:ℂ)‖ := norm_pos_iff.mpr hne
  have hj := sum_zeroMultiplicity_le_jensen chi hchi S
    (c := (contourJensenCenter T:ℂ)) (r := contourJensenCenter T-1/10)
    (R := contourJensenCenter T-1/20) (M := 40*q*contourJensenCenter T)
    (by linarith) (by linarith) (by nlinarith) hne
    (fun rho hr => contour_zero_mem_disk hT (hS rho hr).1 (hS rho hr).2.1 (hS rho hr).2.2)
    (fun z hz => norm_LFunction_contour_disk chi hchi hT (Metric.sphere_subset_closedBall hz))
  have hi := norm_inv_LFunction_le_absoluteZetaTwo chi
    (s := (contourJensenCenter T:ℂ)) (by simpa using (show 2 ≤ contourJensenCenter T by linarith))
  rw [norm_inv] at hi
  have hnum : Real.log (40*q*contourJensenCenter T /
      ‖chi.LFunction (contourJensenCenter T:ℂ)‖) ≤ 40*absoluteZetaTwo*q*contourJensenCenter T := by
    have hl := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < 40*(q:ℝ)*contourJensenCenter T) hn)
    have hm := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 40*(q:ℝ)*contourJensenCenter T by positivity)
    rw [← div_eq_mul_inv] at hm
    nlinarith
  have hd := contour_jensen_log_lower hT
  have hdp : 0 < Real.log ((contourJensenCenter T-1/20)/(contourJensenCenter T-1/10)) :=
    (by positivity : 0 < 1/(20*contourJensenCenter T)).trans_le hd
  apply hj.trans
  apply (div_le_iff₀ hdp).mpr
  have hp : 0 ≤ 800*absoluteZetaTwo*q*(contourJensenCenter T)^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hd hp
  have he : (800*absoluteZetaTwo*q*(contourJensenCenter T)^2) /
      (20*contourJensenCenter T) = 40*absoluteZetaTwo*q*contourJensenCenter T := by
    field_simp
    ring
  rw [mul_one_div, he] at hm
  have hpow : 800*absoluteZetaTwo*q*(contourJensenCenter T)^2 =
      8000000*absoluteZetaTwo*q*(T+4)^4 := by unfold contourJensenCenter; ring
  rw [hpow] at hm
  exact hnum.trans hm

end Ostmann.Dirichlet

end

end OAI
