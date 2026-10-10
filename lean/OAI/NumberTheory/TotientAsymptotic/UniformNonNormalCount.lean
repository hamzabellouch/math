import OAI.NumberTheory.TotientAsymptotic.SqrtCountingCutoff

namespace OAI

/-! Uniform form of the non-normal-prime value exception. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem uniform_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ (S x : ℝ) (J : ℕ),2 < S → 0 ≤ B S → 256 ≤ x → 1 ≤ J →
    x ≤ (2:ℝ)^J → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
      (B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,D,hC,hD,hcount⟩ := non_normal_value_count_split
  refine ⟨C+5*D,by positivity,?_⟩
  intro S x J hS hBS hx hJ hxJ Q hQ
  let N := ⌊Real.sqrt x⌋₊
  let L := Nat.clog 2 N
  have hcut := sqrt_counting_cutoff hx
  have hN : 4 ≤ N := hcut.1
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNx : (N:ℝ) ≤ x := by nlinarith only [hcut.2.1,hNR]
  have hNJ : N ≤ 2^J := by exact_mod_cast hNx.trans hxJ
  have hLJ : L ≤ J := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hNJ
  have hb := dyadic_nat_bounds (show 1 < N by omega)
  have hL1 : 1 ≤ L := hb.1
  have hLlog : 1+Real.log L ≤ 1+Real.log J := by
    exact add_le_add le_rfl (Real.log_le_log (by exact_mod_cast (show 0 < L by omega))
      (by exact_mod_cast hLJ))
  have hLlog0 : 0 ≤ 1+Real.log L := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ L by exact_mod_cast hL1)
    linarith
  have hJlog1 : 1 ≤ 1+Real.log J := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ J by exact_mod_cast hJ)
    linarith
  have hpow2x : (2:ℝ)^L ≤ 2*x := by nlinarith only [hb.2.1,hNx]
  have hBsmall0 : 0 ≤ B ((2:ℝ)^L) := by
    have h4 : 4 ≤ (2:ℕ)^L := hN.trans (Nat.le_pow_clog (by norm_num : 1 < 2) N)
    have hh := (doubleLog_nat_pos h4).le
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hB : B ((2:ℝ)^L) ≤ B (2*x) := by
    have hp : (1:ℝ) < 2^L := by
      have h4 : 4 ≤ (2:ℕ)^L := hN.trans (Nat.le_pow_clog (by norm_num : 1 < 2) N)
      exact_mod_cast (show 1 < (2:ℕ)^L by omega)
    exact Real.log_le_log (Real.log_pos hp) (Real.log_le_log (by positivity) hpow2x)
  have hB0 : 0 ≤ B (2*x) := hBsmall0.trans hB
  have hmass : (B ((2:ℝ)^L))^5*(1+Real.log L) ≤ (B (2*x))^5*(1+Real.log J) :=
    mul_le_mul (pow_le_pow_left₀ hBsmall0 hB 5) hLlog hLlog0 (pow_nonneg hB0 _)
  have hE1 : 1 ≤ dyadicTotientEnvelope J := dyadicTotientEnvelope_one_le J
  have hE0 : 0 ≤ dyadicTotientEnvelope J := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hsn : 0 ≤ (Real.log S)^(-1/6:ℝ) := Real.rpow_nonneg hlogS.le _
  have hlarge : 1+4*dyadicTotientEnvelope J*(1+Real.log J) ≤
      5*dyadicTotientEnvelope J*(1+Real.log J) := by
    have hh := mul_le_mul hE1 hJlog1 (by norm_num) hE0
    nlinarith only [hh]
  have hs : C*dyadicTotientEnvelope J*x/Real.log x*
      (B ((2:ℝ)^L))^5*(1+Real.log L)*(Real.log S)^(-1/6:ℝ) ≤
      C*dyadicTotientEnvelope J*x/Real.log x*
        (B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (show 0 ≤ C*dyadicTotientEnvelope J*x/Real.log x by positivity)) hsn
    convert hh using 1 <;> ring
  have hl : (D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
      (1+4*dyadicTotientEnvelope J*(1+Real.log J)) ≤
      (5*D)*dyadicTotientEnvelope J*x/Real.log x*(B (2*x))^5*(1+Real.log J)*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlarge
      (show 0 ≤ D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) by positivity)
    convert hh using 1
    ring
  have hc := hcount S x N J hS hBS hN (by linarith) hcut.2.1 hcut.2.2 hJ hxJ Q hQ
  exact hc.trans ((add_le_add hs hl).trans_eq (by ring))

end TotientAsymptotic

end

end OAI
