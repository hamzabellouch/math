import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselBounds

namespace OAI

/-! Explicit arbitrary power majorants for the cubic theta kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma pow_mul_exp_neg_le_factorial (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y^k*Real.exp (-y) ≤ k.factorial := by
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp y hy k)
  calc
    _ ≤ (Real.exp y*(k.factorial:ℝ))*Real.exp (-y) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [mul_right_comm,←Real.exp_add]; simp

lemma exp_neg_div_le_power (k : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    Real.exp (-x/t) ≤ (k.factorial:ℝ)*t^k/x^k := by
  have h := pow_mul_exp_neg_le_factorial k (div_pos hx ht).le
  rw [div_pow] at h
  apply (le_div_iff₀ (pow_pos hx k)).mpr
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg ht.le k)
  simpa only [neg_div] using (show Real.exp (-(x/t))*x^k ≤ (k.factorial:ℝ)*t^k by
    convert hh using 1; field_simp)

lemma cubicBesselHeat_power_bound (k : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    cubicBesselHeat x t ≤ ((k.factorial:ℝ)/x^k)*
      (t^((k:ℝ)-4/3)*Real.exp (-t)) := by
  unfold cubicBesselHeat
  calc
    _ ≤ (t^(-4/3:ℝ)*Real.exp (-t))*((k.factorial:ℝ)*t^k/x^k) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_le_power k hx ht) (by positivity)
    _ = _ := by
      rw [←Real.rpow_natCast t k]
      have he : t^(-4/3:ℝ)*t^(k:ℝ) = t^((k:ℝ)-4/3) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((k.factorial:ℝ)/x^k)*(t^(-4/3:ℝ)*t^(k:ℝ))*Real.exp (-t) := by ring
        _ = _ := by rw [he]; ring

/-- The power is arbitrary; the coefficient is the exact Gamma integral of
its positive majorant. This is used for summing the actual theta series. -/
theorem cubicBesselKernel_power_bound (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    cubicBesselKernel x ≤ ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3))*
      x^(1/6-(k:ℝ)) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 < (k:ℝ)-1/3 := by linarith
  have hefun : (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t)) =
      (fun t : ℝ => t^(((k:ℝ)-1/3)-1)*Real.exp (-1*t)) := by
    funext t
    rw [show (k:ℝ)-1/3-1 = (k:ℝ)-4/3 by ring]
    simp
  have hi : IntegrableOn (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t)) (Ioi 0) := by
    rw [hefun]
    exact integrable_laplace_rpow ha (by norm_num : (0:ℝ) < 1)
  have hb := integral_mono_ae (cubicBesselHeat_integrable hx)
    (hi.const_mul ((k.factorial:ℝ)/x^k)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselHeat_power_bound k hx ht)
  have he : (∫ t in Ioi (0:ℝ), t^((k:ℝ)-4/3)*Real.exp (-t)) = Real.Gamma ((k:ℝ)-1/3) := by
    rw [hefun,laplace_rpow ha (by norm_num : (0:ℝ) < 1)]
    simp
  calc
    _ ≤ x^(1/6:ℝ)*(((k.factorial:ℝ)/x^k)*Real.Gamma ((k:ℝ)-1/3)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
      simpa only [integral_const_mul,he] using hb
    _ = _ := by
      rw [Real.rpow_sub hx,Real.rpow_natCast]
      ring

end CubicFirstMoment

end

end OAI
