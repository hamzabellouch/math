import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusFourierSmooth

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma spectral_shift_exp_bound {lam gap rate T R t : ℝ}
    (hlam : 0≤lam) (hgap : 0≤gap) (hrate : lam+gap≤rate)
    (hT : R+1≤T) (ht : -R≤t) :
    exp (lam*T)*exp (-rate*(T+t)) ≤
      exp (lam*(R+1))*exp (-gap*(T-R-1))*exp (-rate) := by
  rw [←exp_add,←exp_add,←exp_add]
  apply exp_le_exp.mpr
  have hr : 0≤rate := le_trans (add_nonneg hlam hgap) hrate
  have h1 := mul_nonneg (sub_nonneg.mpr hrate) (show 0≤T-R-1 by linarith)
  have h2 := mul_nonneg hr (show 0≤t+R by linarith)
  nlinarith

lemma flatFourier_shift_uniform_bound {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B lam gap R T : ℝ}
    (ha : ∀ h, |a h|≤B) (hlam : 0≤lam) (hgap : 0≤gap)
    (hsep : ∀ h, a h≠0 → lam+gap≤torusRate s h) (hT : R+1≤T)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : -R≤x 0) :
    exp (lam*T)*‖iteratedFDeriv ℝ n (flatFourier s a phase) (x+![T,0,0])‖ ≤
      (exp (lam*(R+1))*exp (-gap*(T-R-1)))*
        ∑' h, B*((torusRate s h+torusSize h)^n*exp (-torusRate s h)) := by
  have hy : 0<(x+![T,0,0]) 0 := by
    simp only [Pi.add_apply,Matrix.cons_val_zero]; linarith
  rw [flatFourier_iterated hs ha n hy]
  let C := exp (lam*(R+1))*exp (-gap*(T-R-1))
  have hC : 0≤C := by dsimp [C]; positivity
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  have hb : Summable (fun h => B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))) := by
    simpa using (flatMode_derivative_summable hs n (show (0:ℝ)<1 by norm_num)).mul_left B
  have hi (h : Fin 2 → ℤ) :
      exp (lam*T)*‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖ ≤
        C*(B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))) := by
    by_cases hz : a h=0
    · simp only [hz,zero_mul,iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero,mul_zero]
      exact mul_nonneg hC (mul_nonneg hB (mul_nonneg (pow_nonneg (add_nonneg (sqrt_nonneg _) (torusSize_nonneg h)) n) (exp_nonneg _)))
    have hp : 0≤(torusRate s h+torusSize h)^n := by
      have := torusSize_nonneg h
      dsimp [torusRate]; positivity
    have h1 := mul_le_mul_of_nonneg_right (ha h) hp
    have h2 := spectral_shift_exp_bound hlam hgap (hsep h hz) hT hx
    have h3 := mul_le_mul h1 h2 (by positivity) (mul_nonneg hB hp)
    have hd := weighted_phase_iterated_bound (s:=s) (h:=h) (phase h) (a h) n (x+![T,0,0])
    apply (mul_le_mul_of_nonneg_left hd (exp_nonneg _)).trans
    simpa only [Pi.add_apply,Matrix.cons_val_zero,C,add_comm,mul_assoc,mul_left_comm,mul_comm] using h3
  have hn : Summable (fun h => ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖) := by
    have hδ : 0<(x+![T,0,0]) 0/2 := by positivity
    exact Summable.of_nonneg_of_le (fun h => norm_nonneg _)
      (fun h => weighted_phase_halfspace_bound ha n h (by linarith : (x+![T,0,0]) 0/2≤(x+![T,0,0]) 0))
      ((flatMode_derivative_summable hs n hδ).mul_left B)
  calc
    _ ≤ exp (lam*T)*(∑' h, ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (exp_nonneg _)
    _ = ∑' h, exp (lam*T)*‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖ := tsum_mul_left.symm
    _ ≤ ∑' h, C*(B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))) :=
      (hn.mul_left _).tsum_le_tsum hi (hb.mul_left C)
    _ = _ := tsum_mul_left

end ScalarConductivity

end
end

end OAI
