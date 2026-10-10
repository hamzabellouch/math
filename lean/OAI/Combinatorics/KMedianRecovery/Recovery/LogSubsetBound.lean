import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.FinSets

namespace OAI

namespace MetricKMedianRecovery.LogPolynomial
lemma binary_exponential (A : ℝ) : ∃ d : ℕ, ∀ N b : ℕ,
    (b:ℝ)≤A*Real.log ((N:ℝ)+2) → 2^b≤(N+2)^d := by
  refine ⟨⌈A*Real.log 2⌉₊,?_⟩
  intro N b hb
  have hN : 0<(N:ℝ)+2 := by positivity
  have hlog : 0≤Real.log ((N:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have h2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hm : (b:ℝ)*Real.log 2 ≤ (⌈A*Real.log 2⌉₊:ℝ)*Real.log ((N:ℝ)+2) := by
    calc
      _ ≤ (A*Real.log ((N:ℝ)+2))*Real.log 2 := mul_le_mul_of_nonneg_right hb h2
      _ = (A*Real.log 2)*Real.log ((N:ℝ)+2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog
  have hh := Real.exp_le_exp.mpr hm
  simp only [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_log hN] at hh
  exact_mod_cast hh
end MetricKMedianRecovery.LogPolynomial
namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
lemma source_capacity (A : ℝ) : ∃ d : ℕ, ∀ {n : ℕ} (ctx : List Bool) (U : Finset (Fin n)) (N : ℕ),
    N≤(pairBits (ctx,BinaryFinSet.encode U)).length →
    (U.card:ℝ)≤A*Real.log ((N:ℝ)+2) →
    2^U.card*(2*(BinaryFinSet.encode U).length+2)≤((pairBits (ctx,BinaryFinSet.encode U)).length+1)^d := by
  obtain ⟨e,he⟩:=LogPolynomial.binary_exponential A
  refine ⟨2*e+2,?_⟩
  intro n ctx U N hN hU
  let L:=(pairBits (ctx,BinaryFinSet.encode U)).length
  have hL : 1≤L := by dsimp [L];simp only [pairBits_length];omega
  have hk : (BinaryFinSet.encode U).length≤L := by dsimp [L];simp only [pairBits_length];omega
  have hd : N+2≤(L+1)^2 := by nlinarith
  have hp: 2^U.card≤(L+1)^(2*e) := by
    calc
      _ ≤ (N+2)^e := he N U.card hU
      _ ≤ ((L+1)^2)^e := Nat.pow_le_pow_left hd e
      _ = _ := by rw [pow_mul]
  have hx : 2*(BinaryFinSet.encode U).length+2≤(L+1)^2 := by nlinarith
  calc
    _ ≤ (L+1)^(2*e)*(L+1)^2 := Nat.mul_le_mul hp hx
    _ = _ := by rw [pow_add]
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
