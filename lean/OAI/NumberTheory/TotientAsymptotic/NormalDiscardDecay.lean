import OAI.NumberTheory.TotientAsymptotic.PrimeDiscardCutoff
import OAI.NumberTheory.TotientAsymptotic.FordCollisionCutoffs
import OAI.NumberTheory.TotientAsymptotic.CofactorShellDecay

namespace OAI

/-! Absorb the short suffix entropy and both index choices in the normality saving. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normal_discard_geometric {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∀ᶠ h : ℕ in atTop, ∀ b : ℝ, (h : ℝ)^12 ≤ b → Real.log (6*b) ≤ 26*h →
    ∀ n : ℕ, n ≤ h →
      (h : ℝ)^2*(C*(2*b+2)^6*Real.exp (-(b^(1/3 : ℝ))/6))*(D*(2*b+2))^n ≤ rho^h := by
  let A := |Real.log C|+|Real.log D|+lam+200
  have hA : 200 ≤ A := by dsimp [A]; linarith [abs_nonneg (Real.log C),abs_nonneg (Real.log D),lam_pos]
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop A)] with h hh
  intro b hb hlog n hn
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hb1 : (1 : ℝ) ≤ b := (one_le_pow₀ hh1).trans hb
  have hb0 : 0 < b := by linarith
  have hroot : (h : ℝ)^4 ≤ b^(1/3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hb0.le _) (by norm_num : 3 ≠ 0)).mp
    have he : (b^(1/3 : ℝ))^3=b := by
      rw [← Real.rpow_mul_natCast hb0.le]
      norm_num
    rw [he]
    convert hb using 1; ring
  have hbase : 0 < 2*b+2 := by linarith
  have hlogbase : Real.log (2*b+2) ≤ 26*h :=
    (Real.log_le_log hbase (by linarith : 2*b+2 ≤ 6*b)).trans hlog
  have hlogh : Real.log (h : ℝ) ≤ h := by linarith [Real.log_le_sub_one_of_pos hh0]
  have hnR : (n : ℝ) ≤ h := by exact_mod_cast hn
  have hcoeff : 0 ≤ |Real.log D|+26*(h : ℝ) := by positivity
  have hnt : (n : ℝ)*(Real.log D+Real.log (2*b+2)) ≤
      (h : ℝ)*(|Real.log D|+26*h) :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnR hcoeff)
  have hh2 : (h : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hsmall : |Real.log C|+(158+|Real.log D|+lam)*(h : ℝ)+26*(h : ℝ)^2 ≤ A*(h : ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (h : ℝ)^2 by nlinarith)
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 158+|Real.log D|+lam by linarith [abs_nonneg (Real.log D),lam_pos])
    dsimp [A]
    nlinarith
  have hlarge : 6*A ≤ (h : ℝ)^2 := by nlinarith
  have hextra := mul_nonneg (show 0 ≤ (h : ℝ)^2 by positivity) (sub_nonneg.mpr hlarge)
  have hexponent : 2*Real.log (h : ℝ)+Real.log C+6*Real.log (2*b+2)+
      (n : ℝ)*(Real.log D+Real.log (2*b+2))-b^(1/3 : ℝ)/6 ≤ -lam*h := by
    nlinarith [le_abs_self (Real.log C)]
  have heq : (h : ℝ)^2*(C*(2*b+2)^6*Real.exp (-(b^(1/3 : ℝ))/6))*(D*(2*b+2))^n =
      Real.exp (2*Real.log (h : ℝ)+Real.log C+6*Real.log (2*b+2)+
        (n : ℝ)*(Real.log D+Real.log (2*b+2))-b^(1/3 : ℝ)/6) := by
    have htwo : Real.exp (2*Real.log (h : ℝ))=(h : ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h : ℝ)) 2
    have hsix : Real.exp (6*Real.log (2*b+2))=(2*b+2)^6 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hbase] using Real.exp_nat_mul (Real.log (2*b+2)) 6
    rw [Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add,htwo,hsix,
      Real.exp_nat_mul,Real.exp_log hC,Real.exp_add,Real.exp_log hD,Real.exp_log hbase]
    rw [show -(b^(1/3 : ℝ))/6= -(b^(1/3 : ℝ)/6) by ring,Real.exp_neg]
    ring

  rw [heq]
  apply (Real.exp_le_exp.mpr hexponent).trans_eq
  have hlogrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(h : ℝ)=(h : ℝ)*Real.log rho by rw [hlogrho]; ring,Real.exp_nat_mul,Real.exp_log rho_pos]

end TotientAsymptotic

end

end OAI
