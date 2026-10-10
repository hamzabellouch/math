import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleMeanValue
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! The coefficient window used in the double mean-value specialization. -/
namespace TwoPointCorrelations

open Finset

noncomputable def halaszDoubleWindow {k : ℕ} (r M : ℕ) (j : Fin k) : ℝ :=
  1/(16*(r:ℝ)*(M:ℝ)^(j.val+1))

lemma halasz_double_window_pos {k r M : ℕ} (hr : 1≤r) (hM : 1≤M) (j : Fin k) :
    0<halaszDoubleWindow r M j := by
  have hrR : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hMR : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  unfold halaszDoubleWindow
  positivity

lemma halasz_double_window_small {k r M : ℕ} (hr : 1≤r) (hM : 1≤M) (j : Fin k) :
    halaszDoubleWindow r M j≤1/4 := by
  have hrR : 1≤(r:ℝ) := by exact_mod_cast hr
  have hMR : 1≤(M:ℝ) := by exact_mod_cast hM
  have hp : 1≤(M:ℝ)^(j.val+1) := one_le_pow₀ hMR
  have hd : 16≤16*(r:ℝ)*(M:ℝ)^(j.val+1) := by nlinarith
  unfold halaszDoubleWindow
  apply (div_le_iff₀ (by linarith : 0<16*(r:ℝ)*(M:ℝ)^(j.val+1))).mpr
  linarith

lemma halasz_double_window_phase {k r M : ℕ} (hr : 1≤r) (hM : 1≤M) (j : Fin k) :
    2*Real.pi*((r*M^(j.val+1):ℕ):ℝ)*halaszDoubleWindow r M j≤1 := by
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have hM0 : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have he : 2*Real.pi*((r*M^(j.val+1):ℕ):ℝ)*halaszDoubleWindow r M j=Real.pi/8 := by
    unfold halaszDoubleWindow
    push_cast
    field_simp [hr0,hM0]
    ring
  rw [he]
  linarith [Real.pi_lt_four]

lemma halasz_double_window_product {k r M : ℕ} (hr : 1≤r) (hM : 1≤M) :
    (∏ j : Fin k,halaszDoubleWindow r M j)*
      ((16*(r:ℝ))^k*(M:ℝ)^(∑ j : Fin k, (j.val+1)))=1 := by
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have hM0 : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have he (j : Fin k) : halaszDoubleWindow r M j*(16*(r:ℝ)*(M:ℝ)^(j.val+1))=1 := by
    unfold halaszDoubleWindow
    exact one_div_mul_cancel (mul_ne_zero (mul_ne_zero (by norm_num) hr0) (pow_ne_zero _ hM0))
  calc
    _ = (∏ j : Fin k,halaszDoubleWindow r M j)*
        (∏ j : Fin k,16*(r:ℝ)*(M:ℝ)^(j.val+1)) := by
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,prod_pow_eq_pow_sum]
    _ = ∏ j : Fin k,halaszDoubleWindow r M j*(16*(r:ℝ)*(M:ℝ)^(j.val+1)) :=
      (prod_mul_distrib).symm
    _ = 1 := by simp only [he,prod_const_one]

end TwoPointCorrelations

end OAI
