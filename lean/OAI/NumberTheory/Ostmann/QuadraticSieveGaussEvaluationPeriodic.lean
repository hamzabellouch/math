import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationGaussian

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex Filter
open scoped Topology BigOperators

def periodicGaussian (q : ℕ) [NeZero q] (w : Fin q → ℂ) (b : ℂ) : ℂ :=
  ∑' n : ℤ, w ((Int.divModEquiv q n).2)*gaussianWave b n

theorem summable_periodicGaussian (q : ℕ) [NeZero q] (w : Fin q → ℂ)
    {b : ℂ} (hb : 0<b.re) :
    Summable (fun n : ℤ => w ((Int.divModEquiv q n).2)*gaussianWave b n) := by
  have hw (a : Fin q) : ‖w a‖≤∑ i : Fin q, ‖w i‖ :=
    Finset.single_le_sum (fun i _ => norm_nonneg (w i)) (Finset.mem_univ a)
  apply ((summable_gaussianWave hb).norm.mul_left (∑ i : Fin q, ‖w i‖)).of_norm_bounded
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)

theorem periodicGaussian_residue_sum (q : ℕ) [NeZero q] (w : Fin q → ℂ)
    {b : ℂ} (hb : 0<b.re) :
    periodicGaussian q w b = ∑ a : Fin q, w a *
      ∑' n : ℤ, gaussianWave (b*(q : ℂ)^2) ((a.val : ℝ)/q+n) := by
  let e : ℤ ≃ Fin q × ℤ := (Int.divModEquiv q).trans (Equiv.prodComm _ _)
  let F : Fin q × ℤ → ℂ := fun p => w p.1*
    gaussianWave (b*(q : ℂ)^2) ((p.1.val : ℝ)/q+p.2)
  have hq : (q : ℝ)≠0 := by exact_mod_cast NeZero.ne q
  have hqc : (q : ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hF (n : ℤ) : w ((Int.divModEquiv q n).2)*gaussianWave b n = F (e n) := by
    have hr : ((Int.divModEquiv q n).1 : ℝ)*(q : ℝ)+
        ((Int.divModEquiv q n).2.val : ℝ)=(n : ℝ) := by
      exact_mod_cast (Int.divModEquiv q).symm_apply_apply n
    have hr' : (((Int.divModEquiv q n).2.val : ℝ)/q+
      ((Int.divModEquiv q n).1 : ℝ))*(q : ℝ)=(n : ℝ) := by field_simp; linarith
    change w ((Int.divModEquiv q n).2)*gaussianWave b n =
      w ((Int.divModEquiv q n).2)*gaussianWave (b*(q : ℂ)^2)
        (((Int.divModEquiv q n).2.val : ℝ)/q+((Int.divModEquiv q n).1 : ℝ))
    congr 1
    unfold gaussianWave
    congr 1
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr'
    push_cast at hc ⊢
    rw [←hc]
    ring
  have hFsum : Summable F := by
    have hh := (summable_periodicGaussian q w hb).comp_injective e.symm.injective
    apply hh.congr
    intro p
    simpa only [Function.comp_def,e.apply_symm_apply] using hF (e.symm p)
  calc
    _ = ∑' n : ℤ, F (e n) := tsum_congr hF
    _ = ∑' p : Fin q × ℤ, F p := e.tsum_eq F
    _ = ∑' a : Fin q, ∑' n : ℤ, F (a,n) := hFsum.tsum_prod
    _ = _ := by simp only [tsum_fintype,F,tsum_mul_left]

theorem gaussian_scaled_re (b : ℂ) (q : ℕ) :
    (b*(q : ℂ)^2).re=b.re*(q : ℝ)^2 := by
  have h : (q : ℂ)^2=(((q : ℝ)^2 : ℝ) : ℂ) := by norm_cast
  have hr : ((q : ℂ)^2).re=(q : ℝ)^2 := congrArg Complex.re h
  have hi : ((q : ℂ)^2).im=0 := congrArg Complex.im h
  rw [Complex.mul_re,hr,hi,mul_zero,sub_zero]

theorem gaussian_scaled_inv_re (b : ℂ) (q : ℕ) :
    ((b*(q : ℂ)^2)⁻¹).re=(b⁻¹).re/(q : ℝ)^2 := by
  rw [mul_inv_rev]
  have h : ((q : ℂ)^2)⁻¹=(((q : ℝ)^2)⁻¹ : ℝ) := by push_cast; rfl
  rw [h,Complex.re_ofReal_mul]
  ring

theorem periodicGaussian_tendsto {T : Type*} {l : Filter T} (q : ℕ) [NeZero q]
    (w : Fin q → ℂ) (b : T → ℂ) (hb : ∀ᶠ t in l, 0<(b t).re)
    (hRe : Tendsto (fun t => ((b t)⁻¹).re) l atTop) :
    Tendsto (fun t => (b t*(q : ℂ)^2)^(1/2 : ℂ)*periodicGaussian q w (b t))
      l (𝓝 (∑ a : Fin q, w a)) := by
  have hq : 0<(q : ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast NeZero.ne q)
  have hsRe : Tendsto (fun t => ((b t*(q : ℂ)^2)⁻¹).re) l atTop := by
    simpa only [gaussian_scaled_inv_re,div_eq_mul_inv] using
      hRe.atTop_mul_const (inv_pos.mpr hq)
  have hsb : ∀ᶠ t in l, 0<(b t*(q : ℂ)^2).re := by
    filter_upwards [hb] with t ht
    rw [gaussian_scaled_re]
    exact mul_pos ht hq
  have hsum := tendsto_finsetSum Finset.univ (fun a _ =>
    (normalized_shifted_gaussian_tendsto (fun t => b t*(q : ℂ)^2) hsb hsRe
      ((a.val : ℝ)/q)).const_mul (w a))
  simp only [mul_one] at hsum
  apply hsum.congr'
  filter_upwards [hb] with t ht
  rw [periodicGaussian_residue_sum q w ht,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

end Ostmann.QuadraticSieve

end

end OAI
