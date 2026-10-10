import OAI.NumberTheory.TotientAsymptotic.LocalNormalityMass
import OAI.NumberTheory.TotientAsymptotic.PPTNormalWitnessCount
import OAI.NumberTheory.TotientAsymptotic.CountingEnvelopeReal

namespace OAI

/-! Nonnormal preimages at a local residual endpoint, with the actual value envelope. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma local_value_normality_decay_rate {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ u : ℝ,1 ≤ u → Real.log u ≤ A*h →
      C*Real.exp (9*(Real.log u)^2)*u^6*Real.exp (-(h:ℝ)^4/6) ≤ rho^(K*h) := by
  let M := |Real.log C|+9*A^2+6*A+K*lam+1
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith only [abs_nonneg (Real.log C),sq_nonneg A,hA,lam_pos,mul_nonneg (Nat.cast_nonneg K) lam_pos.le]
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (6*M))] with h hh
  intro u hu hlog
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hh1 : (1:ℝ) ≤ h := by nlinarith only [hh,hM]
  have hh2 : (h:ℝ) ≤ (h:ℝ)^2 := by nlinarith only [hh1]
  have hlu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlog2 : (Real.log u)^2 ≤ A^2*(h:ℝ)^2 := by
    exact (pow_le_pow_left₀ hlu hlog 2).trans_eq (by ring)
  have hconst := mul_le_mul_of_nonneg_left
    (show (1:ℝ)≤(h:ℝ)^2 by nlinarith only [hh1]) (abs_nonneg (Real.log C))
  have hlinear := mul_le_mul_of_nonneg_left hh2
    (show 0 ≤ 6*A+K*lam from add_nonneg (mul_nonneg (by norm_num) hA)
      (mul_nonneg (Nat.cast_nonneg K) lam_pos.le))
  have hsmall : Real.log C+9*(Real.log u)^2+6*Real.log u+(K*lam)*h ≤ M*(h:ℝ)^2 := by
    dsimp [M]
    nlinarith only [hconst,hlinear,hlog2,hlog,le_abs_self (Real.log C),sq_nonneg (h:ℝ)]
  have hlarge : 6*M ≤ (h:ℝ)^2 := by nlinarith only [hh,hh1]
  have hmul := mul_nonneg (sq_nonneg (h:ℝ)) (sub_nonneg.mpr hlarge)
  have he : Real.log C+9*(Real.log u)^2+6*Real.log u-(h:ℝ)^4/6 ≤ -lam*(K*h) := by
    nlinarith only [hsmall,hmul]
  have hp : u^6=Real.exp (6*Real.log u) := by
    simpa only [Nat.cast_ofNat,Real.exp_log hu0] using (Real.exp_nat_mul (Real.log u) 6).symm
  rw [hp,←Real.exp_log hC,←Real.exp_add,←Real.exp_add,←Real.exp_add]
  rw [neg_div,←sub_eq_add_neg]
  apply (Real.exp_le_exp.mpr he).trans_eq
  have hlrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(K*h:ℝ)=((K*h:ℕ):ℝ)*Real.log rho by rw [hlrho,Nat.cast_mul]; ring,
    Real.exp_nat_mul,Real.exp_log rho_pos]

lemma local_value_normality_decay {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) :
    ∀ᶠ h : ℕ in atTop,∀ u : ℝ,1 ≤ u → Real.log u ≤ A*h →
      C*Real.exp (9*(Real.log u)^2)*u^6*Real.exp (-(h:ℝ)^4/6) ≤ rho^h := by
  simpa only [one_mul] using local_value_normality_decay_rate hC hA 1

/-- The singleton-target argument controls arbitrary nonnormal preimages
without any assumption on their multiplicity. -/
theorem local_nonnormal_witness_count_rate {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ (z : ℝ) (d q : ℕ),
      256 ≤ z → 0 ≤ B z → Real.log (B z+4) ≤ A*h → 0 < d →
      ∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ n ∈ R,∀ p : ℕ,p.Prime → p ∣ n → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ n ∈ R,(∃ m ∈ R,m≠n ∧ m.totient=n.totient) → ∃ c ∈ R,F n=c*q) →
      (∀ n ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ n ∈ Q,0<F n ∧ (F n).totient=d*n.totient ∧ ((d*n.totient:ℕ):ℝ)≤z) →
      (Q.card:ℝ) ≤ z/Real.log z*rho^(K*h) := by
  obtain ⟨C,hC,hcount⟩ := ppt_nonnormal_witness_count_bound
  obtain ⟨D,hD,henvelope⟩ := counting_envelope_real_bound
  filter_upwards [local_value_normality_decay_rate (mul_pos hC hD) hA K] with h hdecay
  intro z d q hz hB hlog hd R Q F hQR hR hq hbranch hbad hF
  have hz4 : 4 ≤ z := by linarith only [hz]
  have hb := counting_dyadic_index_bounds hz4
  have hs : 0 ≤ B (localNormalityScale h) := by
    simp only [localNormalityScale,B,Real.log_exp]
    positivity
  have hc := hcount (localNormalityScale h) z (countingDyadicIndex z) d q
    (localNormalityScale_gt_two h) hs hz hb.1 hb.2.1 hd R Q F hQR hR hq hbranch hbad hF
  rw [localNormalityScale_factor] at hc
  have hp := counting_normality_polynomial hz4 hB
  have hen := henvelope z hz4
  have hfac : 0 ≤ z/Real.log z := (div_pos (by linarith only [hz]) (Real.log_pos (by linarith only [hz]))).le
  have hB2 : 0 ≤ B (2*z) := by
    exact hB.trans (Real.log_le_log (Real.log_pos (by linarith only [hz]))
      (Real.log_le_log (by linarith only [hz]) (by linarith only [hz])))
  have hJ : 0 ≤ 1+Real.log (countingDyadicIndex z) := by
    have hh := Real.log_nonneg (show (1:ℝ)≤countingDyadicIndex z by exact_mod_cast hb.1)
    linarith only [hh]
  have hmul := mul_le_mul hen hp
    (mul_nonneg (pow_nonneg hB2 _) hJ) (by positivity)
  have hbound := mul_le_mul_of_nonneg_left hmul hC.le
  have hsave := hdecay (B z+4) (by linarith only [hB]) hlog
  calc
    _ ≤ (z/Real.log z)*(C*(dyadicTotientEnvelope (countingDyadicIndex z)*
        ((B (2*z))^5*(1+Real.log (countingDyadicIndex z))))*Real.exp (-(h:ℝ)^4/6)) := by
      convert hc using 1
      ring
    _ ≤ (z/Real.log z)*((C*D)*Real.exp (9*(Real.log (B z+4))^2)*
        (B z+4)^6*Real.exp (-(h:ℝ)^4/6)) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      have hh := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-(h:ℝ)^4/6)).le
      convert hh using 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave hfac

theorem local_nonnormal_witness_count {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ h : ℕ in atTop,∀ (z : ℝ) (d q : ℕ),
      256 ≤ z → 0 ≤ B z → Real.log (B z+4) ≤ A*h → 0 < d →
      ∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ n ∈ R,∀ p : ℕ,p.Prime → p ∣ n → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ n ∈ R,(∃ m ∈ R,m≠n ∧ m.totient=n.totient) → ∃ c ∈ R,F n=c*q) →
      (∀ n ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ n ∈ Q,0<F n ∧ (F n).totient=d*n.totient ∧ ((d*n.totient:ℕ):ℝ)≤z) →
      (Q.card:ℝ) ≤ z/Real.log z*rho^h := by
  simpa only [one_mul] using local_nonnormal_witness_count_rate hA 1

end TotientAsymptotic

end

end OAI
