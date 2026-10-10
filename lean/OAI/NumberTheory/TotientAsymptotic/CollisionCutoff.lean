import OAI.NumberTheory.TotientAsymptotic.CollisionScale
import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

/-! The exact logarithmic cutoff and polynomially separated collision layers. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def collisionCutoff (h : ℕ) : ℕ := ⌈30*Real.log (h : ℝ)⌉₊

lemma collisionCutoff_bounds {h : ℕ} (hh : 1 ≤ h) :
    30*Real.log (h : ℝ) ≤ collisionCutoff h ∧
    (collisionCutoff h : ℝ) < 30*Real.log (h : ℝ)+1 := by
  have hl : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hl)⟩

lemma collisionCutoff_div_tendsto :
    Tendsto (fun h : ℕ => (collisionCutoff h : ℝ)/h) atTop (nhds 0) := by
  have hl : Tendsto (fun h : ℕ => Real.log (h : ℝ)/(h : ℝ)) atTop (nhds 0) := by
    simpa only [one_mul, add_zero, pow_one, Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun h : ℕ => (1 : ℝ)/(h : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (g := fun h : ℕ => 30*(Real.log (h : ℝ)/h)+1/h)
  · exact Eventually.of_forall fun h => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have ht := div_le_div_of_nonneg_right (collisionCutoff_bounds hh).2.le
      (Nat.cast_nonneg (α := ℝ) h)
    exact ht.trans_eq (by ring)
  · simpa using (hl.const_mul 30).add hi

lemma collisionCutoff_eventually_small :
    ∀ᶠ h : ℕ in atTop, 2*collisionCutoff h < h := by
  filter_upwards [collisionCutoff_div_tendsto.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)), eventually_ge_atTop 1] with h ht hh
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  have ht' := (div_lt_iff₀ hhR).mp ht
  have : (2*collisionCutoff h : ℝ) < h := by nlinarith
  exact_mod_cast this

lemma rho_collisionCutoff_bounds {h : ℕ} (hh : 1 ≤ h) :
    rho/(h : ℝ)^20 ≤ rho^(collisionCutoff h) ∧
    rho^(collisionCutoff h) ≤ 1/(h : ℝ)^18 := by
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  have hlog : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hJ := collisionCutoff_bounds hh
  have hl := collision_lambda_bounds
  have he : Real.exp (-lam) = rho := by simpa using (rho_pow_eq_exp 1).symm
  have hp (k : ℕ) : Real.exp (-(k : ℝ)*Real.log (h : ℝ)) = 1/(h : ℝ)^k := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hhR]
    simp only [one_div]
  rw [rho_pow_eq_exp]
  constructor
  · calc
      _ = Real.exp (-lam-20*Real.log (h : ℝ)) := by
        rw [Real.exp_sub, show Real.exp (20*Real.log (h : ℝ)) = (h : ℝ)^20 by
          simpa only [Nat.cast_ofNat, Real.exp_log hhR] using
            Real.exp_nat_mul (Real.log (h : ℝ)) 20, he]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hJ.2.le lam_pos.le,
          mul_le_mul_of_nonneg_right hl.2.le hlog])
  · calc
      _ ≤ Real.exp (-18*Real.log (h : ℝ)) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hJ.1 lam_pos.le,
          mul_le_mul_of_nonneg_right hl.1.le hlog])
      _ = _ := hp 18

/-- Phase-uniform comparison of the layer at the first collision and the last
layer retained by the logarithmic cutoff. -/
lemma collision_layer_ratio {h : ℕ} (hh : 1 ≤ h)
    (hJ : 2*collisionCutoff h ≤ h) (s : ℝ) :
    rho/(2*(h : ℝ)^20) ≤
      (alpha s*(h-collisionCutoff h : ℕ)/(rho^(h-collisionCutoff h))) /
        (alpha s*h/rho^h) ∧
    (alpha s*(h-collisionCutoff h : ℕ)/(rho^(h-collisionCutoff h))) /
        (alpha s*h/rho^h) ≤ 1/(h : ℝ)^18 := by
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  have hJh : collisionCutoff h ≤ h := by omega
  have hpow : rho^(h-collisionCutoff h)*rho^(collisionCutoff h) = rho^h := by
    rw [← pow_add, Nat.sub_add_cancel hJh]
  have heq : (alpha s*(h-collisionCutoff h : ℕ)/(rho^(h-collisionCutoff h))) /
        (alpha s*h/rho^h) = ((h-collisionCutoff h : ℕ) : ℝ)/h*rho^(collisionCutoff h) := by
    field_simp [(alpha_pos s).ne', hhR.ne', (pow_pos rho_pos _).ne']
    rw [mul_assoc, hpow]
  rw [heq]
  have hscale : (1/2 : ℝ) ≤ ((h-collisionCutoff h : ℕ) : ℝ)/h ∧
      ((h-collisionCutoff h : ℕ) : ℝ)/h ≤ 1 := by
    rw [Nat.cast_sub hJh]
    have hjR : 2*(collisionCutoff h : ℝ) ≤ h := by exact_mod_cast hJ
    constructor
    · apply (le_div_iff₀ hhR).mpr
      linarith
    · apply (div_le_iff₀ hhR).mpr
      have := Nat.cast_nonneg (α := ℝ) (collisionCutoff h)
      linarith
  constructor
  · have ht := mul_le_mul hscale.1 (rho_collisionCutoff_bounds hh).1
      (div_nonneg rho_pos.le (by positivity)) ((by norm_num : (0 : ℝ) ≤ 1/2).trans hscale.1)
    exact le_trans (le_of_eq (by ring)) ht
  · exact (mul_le_mul_of_nonneg_right hscale.2 (pow_pos rho_pos _).le).trans
      (by simpa using (rho_collisionCutoff_bounds hh).2)

end TotientAsymptotic

end

end OAI
