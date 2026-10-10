import OAI.NumberTheory.TotientAsymptotic.SmoothCountingSplit
import OAI.NumberTheory.TotientAsymptotic.LargeFactorNormalityCount

namespace OAI

/-! Smooth shifted integers below the normality sieve cutoff. -/
noncomputable section
namespace TotientAsymptotic

lemma normality_smooth_count : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    Real.exp 2 ≤ N → 1 ≤ B N → 1 ≤ Real.log N/(200*B N) →
    ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ (largestPrimeFactor n:ℝ) ≤ normalityPrimeCutoff N) →
    (Q.card:ℝ) ≤ C*N/(Real.log N)^2 := by
  obtain ⟨C,hC,hM⟩ := mertensProductInput
  refine ⟨8+C^4,by positivity,?_⟩
  intro N hN hBN hL Q hQ
  have hB : 0 < B N := by linarith
  have hN0 : (0:ℝ) < N := (Real.exp_pos 2).trans_le hN
  have hlog2 : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hN
  have hlog : 0 < Real.log N := by linarith
  let K := ⌊normalityPrimeCutoff N⌋₊
  have hcut : Real.exp (2*(Real.log N/(200*B N))) = normalityPrimeCutoff N := by
    unfold normalityPrimeCutoff
    congr 1
    ring
  have hK : 2 ≤ K := (floor_log_endpoint hL hcut.le).1
  have hK0 : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hKupper : Real.log K ≤ Real.log N/(100*B N) := by
    have hh := Real.log_le_log hK0 (Nat.floor_le (Real.exp_pos _).le)
    simpa only [normalityPrimeCutoff,Real.log_exp] using hh
  have hKL : Real.log K ≤ Real.log N := by
    apply hKupper.trans
    apply (div_le_iff₀ (by positivity : 0 < 100*B N)).mpr
    nlinarith
  have hCprod : primeEulerProduct K ≤ C*Real.log N :=
    (hM K hK).trans (mul_le_mul_of_nonneg_left hKL hC.le)
  have he : Real.exp (-(Real.log N/2)/(4*Real.log K)) ≤ Real.exp (-10*B N) := by
    apply Real.exp_le_exp.mpr
    have hu := (le_div_iff₀ (by positivity : 0 < 100*B N)).mp hKupper
    have hl : 10*B N ≤ (Real.log N/2)/(4*Real.log K) := by
      apply (le_div_iff₀ (by positivity : 0 < 4*Real.log K)).mpr
      nlinarith [mul_nonneg hB.le hlogK.le]
    rw [neg_div]
    linarith
  have htail : Real.exp (-(Real.log N/2)/(4*Real.log K))*(primeEulerProduct K)^4 ≤
      C^4/(Real.log N)^2 := by
    have hprod : (primeEulerProduct K)^4 ≤ (C*Real.log N)^4 :=
      pow_le_pow_left₀ (primeEulerProduct_pos K).le hCprod 4
    apply (mul_le_mul he hprod (by positivity) (Real.exp_pos _).le).trans
    apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
    calc
      _ = C^4*(Real.exp (-10*B N)*(Real.exp (B N))^6) := by
        rw [show Real.exp (B N)=Real.log N from Real.exp_log hlog]
        ring
      _ = C^4*Real.exp (-4*B N) := by
        rw [← Real.exp_nat_mul,← Real.exp_add]
        congr 2
        push_cast
        ring
      _ ≤ C^4 := by
        have hh := Real.exp_le_one_iff.mpr (show -4*B N ≤ 0 by linarith)
        nlinarith [show 0 ≤ C^4 by positivity]
  have hsmall : Real.exp (Real.log N/2) ≤ 8*N/(Real.log N)^2 := by
    have hquad := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ Real.log N/2)
    have hh : (Real.log N)^2 ≤ 8*Real.exp (Real.log N/2) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos (Real.log N/2)).le
    have hexp : Real.exp (Real.log N/2)*Real.exp (Real.log N/2) = (N:ℝ) := by
      rw [← Real.exp_add,add_halves,Real.exp_log hN0]
    rw [mul_assoc,hexp] at hmul
    apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
    nlinarith
  have hsplit := smooth_counting_split hK N (Real.log N/2) Q (by
    intro n hn
    obtain ⟨hn0,hnN,hsm⟩ := hQ n hn
    exact ⟨hn0,hnN,Nat.le_floor hsm⟩)
  have hmult := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  calc
    _ ≤ Real.exp (Real.log N/2)+N*(Real.exp (-(Real.log N/2)/(4*Real.log K))*(primeEulerProduct K)^4) := by
      convert hsplit using 1
      ring
    _ ≤ 8*N/(Real.log N)^2+N*(C^4/(Real.log N)^2) := add_le_add hsmall hmult
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
