import OAI.NumberTheory.TotientAsymptotic.OmegaDiscardDecay

namespace OAI

/-! The squarefree cutoff absorbs all short-suffix entropy. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma square_cutoff_large {h : ℕ} {b u : ℝ} (hh : (100 : ℝ) ≤ h)
    (hb : (h : ℝ)^44 ≤ b) (hu : b/(8*(h : ℝ)^20) ≤ u) :
    b*(h : ℝ)^2 ≤ Real.exp u := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hb0 : 0 < b := (pow_pos hh0 44).trans_le hb
  have hu0 : 0 ≤ u := (by positivity : 0 ≤ b/(8*(h : ℝ)^20)).trans hu
  have h128 : (128 : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hp : 128*(h : ℝ)^42 ≤ (h : ℝ)^44 := by
    have ht := mul_le_mul_of_nonneg_right h128 (show 0 ≤ (h : ℝ)^42 by positivity)
    convert ht using 1; ring
  have hnum : 128*b*(h : ℝ)^42 ≤ b^2 := by
    have ht := mul_le_mul_of_nonneg_left (hp.trans hb) hb0.le
    nlinarith
  have hs : b*(h : ℝ)^2 ≤ (b/(8*(h : ℝ)^20))^2/2 := by
    rw [div_pow,div_div]
    apply (le_div_iff₀ (by positivity : 0 < (8*(h : ℝ)^20)^2*2)).mpr
    convert hnum using 1; ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ b/(8*(h : ℝ)^20)) hu 2
  have he := Real.quadratic_le_exp_of_nonneg hu0
  linarith

lemma square_discard_geometric {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∀ᶠ h : ℕ in atTop, ∀ b u : ℝ,
      (h : ℝ)^44 ≤ b → Real.log (6*b) ≤ 26*h → b/(8*(h : ℝ)^20) ≤ u →
      (h : ℝ)^2*(C*Real.exp (4*b))*(D*(2*b+2))^h/Real.exp (Real.exp u) ≤ rho^h := by
  let A := |Real.log C|+|Real.log D|+lam+30
  have hA : 30 ≤ A := by dsimp [A]; linarith [abs_nonneg (Real.log C),abs_nonneg (Real.log D),lam_pos]
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2*A+100))] with h hh
  intro b u hb hlog hu
  have hh100 : (100 : ℝ) ≤ h := by linarith
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hhp : (h : ℝ) ≤ (h : ℝ)^44 := by simpa using pow_le_pow_right₀ hh1 (show 1 ≤ 44 by omega)
  have hhb : (h : ℝ) ≤ b := hhp.trans hb
  have hb0 : 0 < b := hh0.trans_le hhb
  have hb1 : 1 ≤ b := hh1.trans hhb
  have he := square_cutoff_large hh100 hb hu
  have hbase : 0 < 2*b+2 := by linarith
  have hlogbase : Real.log (2*b+2) ≤ 26*h :=
    (Real.log_le_log hbase (by linarith : 2*b+2 ≤ 6*b)).trans hlog
  have hlogh : Real.log (h : ℝ) ≤ h := by linarith [Real.log_le_sub_one_of_pos hh0]
  have hnt : (h : ℝ)*(Real.log D+Real.log (2*b+2)) ≤
      (h : ℝ)*(|Real.log D|+26*h) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) hh0.le
  have hh2 : (h : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hsmall : |Real.log C|+(2+|Real.log D|+lam)*(h : ℝ)+26*(h : ℝ)^2 ≤ A*(h : ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (h : ℝ)^2 by nlinarith)
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 2+|Real.log D|+lam by linarith [abs_nonneg (Real.log D),lam_pos])
    dsimp [A]
    nlinarith
  have hhalf1 : 4*b ≤ b*(h : ℝ)^2/2 := by
    nlinarith [mul_nonneg hb0.le (show 0 ≤ (h : ℝ)^2-8 by nlinarith)]
  have hhalf2 : A*(h : ℝ)^2 ≤ b*(h : ℝ)^2/2 := by
    nlinarith [mul_nonneg (show 0 ≤ b-2*A by linarith) (show 0 ≤ (h : ℝ)^2 by positivity)]
  have hexponent : 2*Real.log (h : ℝ)+Real.log C+4*b+
      (h : ℝ)*(Real.log D+Real.log (2*b+2))-Real.exp u ≤ -lam*h := by
    nlinarith [le_abs_self (Real.log C)]
  have heq : (h : ℝ)^2*(C*Real.exp (4*b))*(D*(2*b+2))^h/Real.exp (Real.exp u) =
      Real.exp (2*Real.log (h : ℝ)+Real.log C+4*b+
        (h : ℝ)*(Real.log D+Real.log (2*b+2))-Real.exp u) := by
    have htwo : Real.exp (2*Real.log (h : ℝ))=(h : ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h : ℝ)) 2
    rw [Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add,htwo,Real.exp_nat_mul,
      Real.exp_add,Real.exp_log hC,Real.exp_log hD,Real.exp_log hbase]
    ring
  rw [heq]
  apply (Real.exp_le_exp.mpr hexponent).trans_eq
  have hlogrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(h : ℝ)=(h : ℝ)*Real.log rho by rw [hlogrho]; ring,Real.exp_nat_mul,Real.exp_log rho_pos]

lemma square_head_discard_geometric {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∀ᶠ h : ℕ in atTop, ∀ b u : ℝ,
      (h : ℝ)^44 ≤ b → Real.log (6*b) ≤ 26*h → b/(8*(h : ℝ)^20) ≤ u →
      (h : ℝ)^2*(C*Real.exp (6*b))*(D*(2*b+2))^h/Real.exp (Real.exp u) ≤ rho^h := by
  let A := |Real.log C|+|Real.log D|+lam+30
  have hA : 30 ≤ A := by dsimp [A]; linarith [abs_nonneg (Real.log C),abs_nonneg (Real.log D),lam_pos]
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2*A+100))] with h hh
  intro b u hb hlog hu
  have hh100 : (100 : ℝ) ≤ h := by linarith
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hhp : (h : ℝ) ≤ (h : ℝ)^44 := by simpa using pow_le_pow_right₀ hh1 (show 1 ≤ 44 by omega)
  have hhb : (h : ℝ) ≤ b := hhp.trans hb
  have hb0 : 0 < b := hh0.trans_le hhb
  have hb1 : 1 ≤ b := hh1.trans hhb
  have he := square_cutoff_large hh100 hb hu
  have hbase : 0 < 2*b+2 := by linarith
  have hlogbase : Real.log (2*b+2) ≤ 26*h :=
    (Real.log_le_log hbase (by linarith : 2*b+2 ≤ 6*b)).trans hlog
  have hlogh : Real.log (h : ℝ) ≤ h := by linarith [Real.log_le_sub_one_of_pos hh0]
  have hnt : (h : ℝ)*(Real.log D+Real.log (2*b+2)) ≤
      (h : ℝ)*(|Real.log D|+26*h) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) hh0.le
  have hh2 : (h : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hsmall : |Real.log C|+(2+|Real.log D|+lam)*(h : ℝ)+26*(h : ℝ)^2 ≤ A*(h : ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (h : ℝ)^2 by nlinarith)
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 2+|Real.log D|+lam by linarith [abs_nonneg (Real.log D),lam_pos])
    dsimp [A]
    nlinarith
  have hhalf1 : 6*b ≤ b*(h : ℝ)^2/2 := by
    nlinarith [mul_nonneg hb0.le (show 0 ≤ (h : ℝ)^2-12 by nlinarith)]
  have hhalf2 : A*(h : ℝ)^2 ≤ b*(h : ℝ)^2/2 := by
    nlinarith [mul_nonneg (show 0 ≤ b-2*A by linarith) (show 0 ≤ (h : ℝ)^2 by positivity)]
  have hexponent : 2*Real.log (h : ℝ)+Real.log C+6*b+
      (h : ℝ)*(Real.log D+Real.log (2*b+2))-Real.exp u ≤ -lam*h := by
    nlinarith [le_abs_self (Real.log C)]
  have heq : (h : ℝ)^2*(C*Real.exp (6*b))*(D*(2*b+2))^h/Real.exp (Real.exp u) =
      Real.exp (2*Real.log (h : ℝ)+Real.log C+6*b+
        (h : ℝ)*(Real.log D+Real.log (2*b+2))-Real.exp u) := by
    have htwo : Real.exp (2*Real.log (h : ℝ))=(h : ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h : ℝ)) 2
    rw [Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add,htwo,Real.exp_nat_mul,
      Real.exp_add,Real.exp_log hC,Real.exp_log hD,Real.exp_log hbase]
    ring
  rw [heq]
  apply (Real.exp_le_exp.mpr hexponent).trans_eq
  have hlogrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(h : ℝ)=(h : ℝ)*Real.log rho by rw [hlogrho]; ring,Real.exp_nat_mul,Real.exp_log rho_pos]

end TotientAsymptotic

end

end OAI
