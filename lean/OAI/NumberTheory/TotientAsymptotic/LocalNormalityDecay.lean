import OAI.NumberTheory.TotientAsymptotic.NormalDiscardDecay

namespace OAI

/-! Indexed normality: a polynomial logarithmic cutoff beats each bounded local tail. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def localNormalityScale (h : ℕ) : ℝ := Real.exp (Real.exp ((h:ℝ)^4))

lemma localNormalityScale_factor (h : ℕ) :
    (Real.log (localNormalityScale h))^(-1/6:ℝ)=Real.exp (-(h:ℝ)^4/6) := by
  rw [localNormalityScale,Real.log_exp,←Real.exp_mul]
  congr 1
  ring

/-- The two index choices and every local tuple coordinate are included
in this bound. The cutoff U may grow exponentially with the tail length. -/
theorem local_normality_geometric_decay {C D A : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hA : 0 ≤ A) :
    ∀ᶠ h : ℕ in atTop,∀ U : ℝ,1 ≤ U → Real.log (6*U) ≤ A*h →
      ∀ n : ℕ,n ≤ h →
        (h:ℝ)^2*(C*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6))*(D*(2*U+2))^n ≤ rho^h := by
  let M := |Real.log C|+|Real.log D|+lam+8*A+10
  have hM : 10 ≤ M := by dsimp [M]; linarith [lam_pos,abs_nonneg (Real.log C),abs_nonneg (Real.log D)]
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (6*M))] with h hh
  intro U hU hlog n hn
  have hh1 : (1:ℝ) ≤ h := by nlinarith only [hM,hh]
  have hh0 : (0:ℝ) < h := zero_lt_one.trans_le hh1
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hbase : 0 < 2*U+2 := by linarith only [hU]
  have hlogbase : Real.log (2*U+2) ≤ A*h :=
    (Real.log_le_log hbase (by linarith only [hU] : 2*U+2 ≤ 6*U)).trans hlog
  have hlogh : Real.log (h:ℝ) ≤ h := Real.log_le_self hh0.le
  have hnR : (n:ℝ) ≤ h := by exact_mod_cast hn
  have hnt : (n:ℝ)*(Real.log D+Real.log (2*U+2)) ≤
      (h:ℝ)*(|Real.log D|+A*h) :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnR (by positivity))
  have hh2 : (h:ℝ) ≤ (h:ℝ)^2 := by nlinarith only [hh1]
  have hsmall : |Real.log C|+(2+6*A+|Real.log D|+lam)*(h:ℝ)+A*(h:ℝ)^2 ≤ M*(h:ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (h:ℝ)^2 by nlinarith only [hh1])
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 2+6*A+|Real.log D|+lam by
        linarith only [hA,abs_nonneg (Real.log D),lam_pos])
    dsimp [M]
    nlinarith only [hc,hd,hA,sq_nonneg (h:ℝ)]
  have hlarge : 6*M ≤ (h:ℝ)^2 := by nlinarith only [hh,hh1]
  have hextra := mul_nonneg (sq_nonneg (h:ℝ)) (sub_nonneg.mpr hlarge)
  have hexponent : 2*Real.log (h:ℝ)+Real.log C+6*Real.log (2*U+2)+
      (n:ℝ)*(Real.log D+Real.log (2*U+2))-(h:ℝ)^4/6 ≤ -lam*h := by
    nlinarith only [hlogh,hlogbase,hnt,hsmall,hextra,le_abs_self (Real.log C)]
  have heq : (h:ℝ)^2*(C*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6))*(D*(2*U+2))^n =
      Real.exp (2*Real.log (h:ℝ)+Real.log C+6*Real.log (2*U+2)+
        (n:ℝ)*(Real.log D+Real.log (2*U+2))-(h:ℝ)^4/6) := by
    have htwo : Real.exp (2*Real.log (h:ℝ))=(h:ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h:ℝ)) 2
    have hsix : Real.exp (6*Real.log (2*U+2))=(2*U+2)^6 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hbase] using Real.exp_nat_mul (Real.log (2*U+2)) 6
    rw [Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add,htwo,hsix,
      Real.exp_nat_mul,Real.exp_log hC,Real.exp_add,Real.exp_log hD,Real.exp_log hbase]
    rw [show -(h:ℝ)^4/6= -((h:ℝ)^4/6) by ring,Real.exp_neg]
    ring
  rw [heq]
  apply (Real.exp_le_exp.mpr hexponent).trans_eq
  have hlogrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(h:ℝ)=(h:ℝ)*Real.log rho by rw [hlogrho]; ring,
    Real.exp_nat_mul,Real.exp_log rho_pos]

end TotientAsymptotic

end

end OAI
