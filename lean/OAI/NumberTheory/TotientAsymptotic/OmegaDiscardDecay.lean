import OAI.NumberTheory.TotientAsymptotic.NormalDiscardDecay

namespace OAI

/-! The large factor-count tail dominates the entropy of all suffix choices. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma omega_discard_geometric {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∀ᶠ h : ℕ in atTop, ∀ b d : ℝ,
      (h : ℝ)^12 ≤ b → Real.log (6*b) ≤ 26*h → d ≤ b/(h : ℝ)^18 →
      ∀ n : ℕ, n ≤ h →
      (h : ℝ)^2*(C*Real.exp (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2)))*
        (D*(2*b+2))^n ≤ rho^h := by
  let A := |Real.log C|+|Real.log D|+lam+30
  have hA : 30 ≤ A := by dsimp [A]; linarith [abs_nonneg (Real.log C),abs_nonneg (Real.log D),lam_pos]
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (12*A+100))] with h hh
  intro b d hb hlog hd n hn
  have hh100 : (100 : ℝ) ≤ h := by linarith
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hb1 : (1 : ℝ) ≤ b := (one_le_pow₀ hh1).trans hb
  have hb0 : 0 < b := by linarith
  have h9 : (72 : ℝ) ≤ (h : ℝ)^9 := by
    have hp := pow_le_pow_right₀ hh1 (show 1 ≤ 9 by omega)
    simp only [pow_one] at hp
    linarith
  have hdsmall : 6*d ≤ b/(12*(h : ℝ)^9) := by
    apply (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 6)).trans
    rw [show 6*(b/(h : ℝ)^18)=(6*b)/(h : ℝ)^18 by ring]
    apply (div_le_div_iff₀ (pow_pos hh0 18) (by positivity : 0 < 12*(h : ℝ)^9)).mpr
    have hp := mul_le_mul_of_nonneg_left h9 (show 0 ≤ b*(h : ℝ)^9 by positivity)
    nlinarith [show (h : ℝ)^18=((h : ℝ)^9)^2 by ring]
  have hlogr : (1/3 : ℝ) ≤ Real.log (3/2) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<3/2)
    norm_num at hh ⊢
    exact hh
  have hT : b/(6*(h : ℝ)^9) ≤ b/(2*(h : ℝ)^9)*Real.log (3/2) := by
    have ht := mul_le_mul_of_nonneg_left hlogr (show 0 ≤ b/(2*(h : ℝ)^9) by positivity)
    convert ht using 1; ring
  have hsaving : 6*d-b/(2*(h : ℝ)^9)*Real.log (3/2) ≤ -(h : ℝ)^3/12 := by
    have hb' : (h : ℝ)^3/12 ≤ b/(12*(h : ℝ)^9) := by
      apply (le_div_iff₀ (by positivity : 0 < 12*(h : ℝ)^9)).mpr
      convert hb using 1; ring
    have he : b/(6*(h : ℝ)^9)=2*(b/(12*(h : ℝ)^9)) := by ring
    linarith
  have hbase : 0 < 2*b+2 := by linarith
  have hlogbase : Real.log (2*b+2) ≤ 26*h :=
    (Real.log_le_log hbase (by linarith : 2*b+2 ≤ 6*b)).trans hlog
  have hlogh : Real.log (h : ℝ) ≤ h := by linarith [Real.log_le_sub_one_of_pos hh0]
  have hnR : (n : ℝ) ≤ h := by exact_mod_cast hn
  have hnt : (n : ℝ)*(Real.log D+Real.log (2*b+2)) ≤
      (h : ℝ)*(|Real.log D|+26*h) :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnR (by positivity))
  have hh2 : (h : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hsmall : |Real.log C|+(2+|Real.log D|+lam)*(h : ℝ)+26*(h : ℝ)^2 ≤ A*(h : ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (h : ℝ)^2 by nlinarith)
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 2+|Real.log D|+lam by linarith [abs_nonneg (Real.log D),lam_pos])
    dsimp [A]
    nlinarith
  have hlarge : 12*A ≤ (h : ℝ) := by linarith
  have hextra := mul_nonneg (show 0 ≤ (h : ℝ)^2 by positivity) (sub_nonneg.mpr hlarge)
  have hexponent : 2*Real.log (h : ℝ)+Real.log C+
      (n : ℝ)*(Real.log D+Real.log (2*b+2))+
      (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2)) ≤ -lam*h := by
    nlinarith [le_abs_self (Real.log C)]
  have heq : (h : ℝ)^2*(C*Real.exp (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2)))*
      (D*(2*b+2))^n = Real.exp (2*Real.log (h : ℝ)+Real.log C+
      (n : ℝ)*(Real.log D+Real.log (2*b+2))+(6*d-b/(2*(h : ℝ)^9)*Real.log (3/2))) := by
    have htwo : Real.exp (2*Real.log (h : ℝ))=(h : ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h : ℝ)) 2
    rw [Real.exp_add,Real.exp_add,Real.exp_add,htwo,Real.exp_nat_mul,Real.exp_add,
      Real.exp_log hC,Real.exp_log hD,Real.exp_log hbase]
    ring
  rw [heq]
  apply (Real.exp_le_exp.mpr hexponent).trans_eq
  have hlogrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(h : ℝ)=(h : ℝ)*Real.log rho by rw [hlogrho]; ring,Real.exp_nat_mul,Real.exp_log rho_pos]

end TotientAsymptotic

end

end OAI
