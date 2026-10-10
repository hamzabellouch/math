import OAI.NumberTheory.TotientAsymptotic.PreimageLinearBound
import OAI.NumberTheory.TotientAsymptotic.PPTSquareWitness

namespace OAI

/-! The square discard at a local endpoint keeps the linear preimage scale. -/
noncomputable section
namespace TotientAsymptotic

lemma square_witness_local_bound {C z : ℝ} {N K : ℕ}
    (_hC : 0 < C) (hz : Real.exp 2 ≤ z) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hsize : (N:ℝ) ≤ C*z*(B z+2)) (hlog : Real.log N ≤ 2*Real.log z)
    (hcut : (Real.log z)^6 ≤ 2*(K:ℝ))
    (S : Finset ℕ) (F : ℕ → ℕ) (hinj : Set.InjOn F (S : Set ℕ))
    (hF : ∀ n ∈ S,0 < F n ∧ F n ≤ N)
    (hsq : ∀ n ∈ S,∃ p : ℕ,p.Prime ∧ K<p ∧ (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) :
    (S.card:ℝ) ≤ 112*C*z*(B z+2)/(Real.log z)^4 := by
  have hz0 : 0 < z := (Real.exp_pos 2).trans_le hz
  have hlz : 2 ≤ Real.log z := (Real.le_log_iff_exp_le hz0).mpr hz
  have hL : 0 < Real.log z := by linarith only [hlz]
  have hK0 : (0:ℝ) < K := by exact_mod_cast (show 0<K by omega)
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog' : (1+Real.log N)^2 ≤ 9*(Real.log z)^2 := by
    have hh : 1+Real.log N ≤ 3*Real.log z := by linarith only [hlog,hlz]
    have hp := pow_le_pow_left₀ (by linarith only [hlog0] : 0≤1+Real.log N) hh 2
    nlinarith only [hp]
  have hnK : (K:ℝ) ≤ ((K+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ K
  have hfirst : 2*(N:ℝ)/((K+1:ℕ):ℝ) ≤ 2*(N:ℝ)/K :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hN0) hK0 hnK
  have hsecond : 6*(N:ℝ)*(1+Real.log N)^2/(K:ℝ) ≤
      54*(N:ℝ)*(Real.log z)^2/(K:ℝ) := by
    apply div_le_div_of_nonneg_right _ hK0.le
    nlinarith only [mul_le_mul_of_nonneg_left hlog' (show 0≤6*(N:ℝ) by positivity)]
  have hsmall : (2*(N:ℝ)+54*(N:ℝ)*(Real.log z)^2)/(K:ℝ) ≤
      56*(N:ℝ)*(Real.log z)^2/(K:ℝ) := by
    apply div_le_div_of_nonneg_right _ hK0.le
    have hh : (1:ℝ) ≤ (Real.log z)^2 := by nlinarith only [hlz]
    nlinarith only [mul_le_mul_of_nonneg_left hh hN0]
  have hcut' : 56*(N:ℝ)*(Real.log z)^2/(K:ℝ) ≤
      112*(N:ℝ)/(Real.log z)^4 := by
    apply (div_le_div_iff₀ hK0 (pow_pos hL 4)).mpr
    have hh := mul_le_mul_of_nonneg_left hcut (show 0≤56*(N:ℝ) by positivity)
    nlinarith only [hh]
  have hc := ppt_square_witness_count hN hK S F hinj hF hsq
  calc
    (S.card:ℝ) ≤ 2*(N:ℝ)/((K+1:ℕ):ℝ)+6*(N:ℝ)*(1+Real.log N)^2/(K:ℝ) := hc
    _ ≤ 2*(N:ℝ)/K+54*(N:ℝ)*(Real.log z)^2/K := add_le_add hfirst hsecond
    _ = (2*(N:ℝ)+54*(N:ℝ)*(Real.log z)^2)/(K:ℝ) := by ring
    _ ≤ 56*(N:ℝ)*(Real.log z)^2/(K:ℝ) := hsmall
    _ ≤ 112*(N:ℝ)/(Real.log z)^4 := hcut'
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_pos hL 4).le
      nlinarith only [hsize]

end TotientAsymptotic

end

end OAI
