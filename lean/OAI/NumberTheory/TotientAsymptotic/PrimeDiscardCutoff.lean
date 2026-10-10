import OAI.NumberTheory.TotientAsymptotic.NormalPrimeMass
import OAI.NumberTheory.TotientAsymptotic.PrimeReciprocalBound

namespace OAI

/-! A common dyadic endpoint for the short suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def discardExponent (b : ℝ) : ℕ := ⌈Real.exp (2*b)⌉₊
def discardPrimeBound (b : ℝ) : ℕ := 2^(discardExponent b)

lemma discardExponent_bounds {b : ℝ} (hb : 2 ≤ b) :
    2 ≤ discardExponent b ∧ Real.log (discardExponent b : ℝ) ≤ 2*b+1 := by
  have he := Real.add_one_le_exp (2*b)
  have hm := Nat.le_ceil (Real.exp (2*b))
  have hm0 : (2 : ℝ) ≤ discardExponent b := by dsimp [discardExponent]; linarith
  refine ⟨by exact_mod_cast hm0,?_⟩
  have hc : (discardExponent b : ℝ) ≤ 2*Real.exp (2*b) := by
    have hu := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (2*b) from (Real.exp_pos _).le)
    dsimp [discardExponent]
    linarith
  calc
    _ ≤ Real.log (2*Real.exp (2*b)) := Real.log_le_log (by linarith) hc
    _ = Real.log 2+2*b := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]

lemma discardPrimeBound_bounds {b : ℝ} (hb : 2 ≤ b) :
    4 ≤ discardPrimeBound b ∧ 0 ≤ B (discardPrimeBound b) ∧
    B (discardPrimeBound b) ≤ 2*b+1 ∧
    Real.exp (Real.exp ((6/5 : ℝ)*b)) ≤ discardPrimeBound b := by
  obtain ⟨hM,hlogM⟩ := discardExponent_bounds hb
  have hM2 : (2 : ℝ) ≤ discardExponent b := by exact_mod_cast hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2up : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  have hlog2low : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hB : B (discardPrimeBound b)=Real.log ((discardExponent b : ℝ)*Real.log 2) := by
    simp only [discardPrimeBound,B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  refine ⟨?_,?_,?_,?_⟩
  · have he := Nat.pow_le_pow_right (by norm_num : 0<2) hM
    exact he
  · rw [hB]
    apply Real.log_nonneg
    nlinarith
  · rw [hB]
    have hh : (discardExponent b : ℝ)*Real.log 2 ≤ discardExponent b := by nlinarith
    exact (Real.log_le_log (by positivity) hh).trans hlogM
  · have he : (2 : ℝ) ≤ Real.exp ((4/5 : ℝ)*b) := by
      linarith [Real.add_one_le_exp ((4/5 : ℝ)*b)]
    have hsplit : Real.exp (2*b)=Real.exp ((6/5 : ℝ)*b)*Real.exp ((4/5 : ℝ)*b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hceil := Nat.le_ceil (Real.exp (2*b))
    change Real.exp (2*b) ≤ (discardExponent b : ℝ) at hceil
    have hh : Real.exp ((6/5 : ℝ)*b) ≤ (discardExponent b : ℝ)*Real.log 2 := by
      rw [hsplit] at hceil
      nlinarith [Real.exp_pos ((6/5 : ℝ)*b)]
    have hNpos : (0 : ℝ) < discardPrimeBound b := by
      unfold discardPrimeBound
      positivity
    apply (Real.le_log_iff_exp_le hNpos).mp
    simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] using hh

lemma discard_normal_mass (hford : FordLemma26Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 2 ≤ b →
      (∑ p ∈ nonNormalPrimes (Real.exp (Real.exp (b^(1/3 : ℝ)))) (discardPrimeBound b),
        ((p-1 : ℕ) : ℝ)⁻¹) ≤
      C*(2*b+2)^6*Real.exp (-(b^(1/3 : ℝ))/6) := by
  obtain ⟨C,hC,hbound⟩ := non_normal_prime_mass hford
  refine ⟨C,hC,?_⟩
  intro b hb
  have hb0 : 0 ≤ b := by linarith
  have hroot : 0 ≤ b^(1/3 : ℝ) := Real.rpow_nonneg hb0 _
  have hS : 2 < Real.exp (Real.exp (b^(1/3 : ℝ))) := by
    have hh := Real.one_le_exp hroot
    have htwo : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    exact htwo.trans_le (Real.exp_le_exp.mpr hh)
  have hBS : 0 ≤ B (Real.exp (Real.exp (b^(1/3 : ℝ)))) := by simpa only [B,Real.log_exp] using hroot
  obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
  have hM := discardExponent_bounds hb
  have he := hbound _ hS hBS _ hN
  rw [show Nat.clog 2 (discardPrimeBound b)=discardExponent b from
    Nat.clog_pow 2 _ (by norm_num)] at he
  have hE : (Real.log (Real.exp (Real.exp (b^(1/3 : ℝ)))))^(-1/6 : ℝ)=
      Real.exp (-(b^(1/3 : ℝ))/6) := by
    rw [Real.log_exp,← Real.exp_mul]
    congr 1
    ring
  rw [hE] at he
  have hBpow : (B ((2 : ℝ)^discardExponent b))^5 ≤ (2*b+2)^5 := by
    apply pow_le_pow_left₀
    · simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBN
    · exact (show B ((2 : ℝ)^discardExponent b) ≤ 2*b+1 by
        simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBU).trans (by linarith)
  calc
    _ ≤ C*(B ((2 : ℝ)^discardExponent b))^5*(1+Real.log (discardExponent b))*
        Real.exp (-(b^(1/3 : ℝ))/6) := he
    _ ≤ C*(2*b+2)^5*(2*b+2)*Real.exp (-(b^(1/3 : ℝ))/6) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul (mul_le_mul_of_nonneg_left hBpow hC.le) (by linarith [hM.2])
      · have hm2 : (1 : ℝ) ≤ discardExponent b := by exact_mod_cast (show 1 ≤ discardExponent b by omega)
        linarith [Real.log_nonneg hm2]
      · positivity
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
