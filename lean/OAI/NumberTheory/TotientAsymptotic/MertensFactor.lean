import OAI.NumberTheory.TotientAsymptotic.MertensLogMass

namespace OAI

/-! Comparison of the ordinary and convergent prime Euler factors. -/
noncomputable section
namespace TotientAsymptotic

lemma mertens_factor_le {u : ℝ} (hu : 0<u) {p : ℕ} (hp : p.Prime) :
    (p : ℝ)/(p-1) ≤ Real.exp (2*u*Real.log p/p)*(1-(p : ℝ)^(-(1+u)))⁻¹ := by
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ)<p := by linarith
  have hd : (0 : ℝ)<p-1 := by linarith
  have hv : 0≤u*Real.log p := mul_nonneg hu.le (Real.log_nonneg (by linarith))
  have hpow : (p : ℝ)^(-(1+u))=(p : ℝ)⁻¹*Real.exp (-(u*Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0]
    have he : Real.log (p : ℝ)*(-(1+u))= -Real.log p+ -(u*Real.log p) := by ring
    rw [he,Real.exp_add,Real.exp_neg,Real.exp_log hp0]
  have hpowlt : (p : ℝ)^(-(1+u))<1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by linarith)
      (show -(1+u)<0 by linarith)
    simpa using h
  have hB : 0<1-(p : ℝ)^(-(1+u)) := by linarith
  have hr : (1 : ℝ)/(p-1)≤2/p := by
    apply (div_le_div_iff₀ hd hp0).mpr
    nlinarith
  have he : (p : ℝ)/(p-1)*(1-(p : ℝ)^(-(1+u))) ≤ Real.exp (2*u*Real.log p/p) := by
    calc
      _ = 1+(1-Real.exp (-(u*Real.log p)))/(p-1) := by
        rw [hpow]
        field_simp
        ring
      _ ≤ 1+(u*Real.log p)/(p-1) := by
        apply add_le_add le_rfl
        apply div_le_div_of_nonneg_right _ hd.le
        linarith [Real.one_sub_le_exp_neg (u*Real.log p)]
      _ ≤ 1+2*u*Real.log p/p := by
        have hh := mul_le_mul_of_nonneg_left hr hv
        convert add_le_add_left hh 1 using 1 <;> ring
      _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (2*u*Real.log p/p)
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hB).mpr he

end TotientAsymptotic

end

end OAI
