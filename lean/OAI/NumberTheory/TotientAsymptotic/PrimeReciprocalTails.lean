import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicLogTail
import OAI.NumberTheory.TotientAsymptotic.UniformPrimeTripleBound
import OAI.NumberTheory.TotientAsymptotic.UniformPrimePairBound

namespace OAI

/-! Reciprocal tails for the two and three linear prime forms in Ford's collision sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_pair_dyadic_count {C : ℝ}
    (hC : ∀ b : ℕ,0 < b → ∀ X : ℕ,2 ≤ X →
      ((allShiftedPrimePairs b X).card:ℝ) ≤ C*X*((b:ℝ)/b.totient)/(Real.log X)^2)
    {b : ℕ} (hb : 0 < b) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q,q.Prime ∧ (b*q+1).Prime) (k : ℕ) (hk : 1 ≤ k) :
    ((Q.filter (fun q => Nat.clog 2 q=k)).card:ℝ) ≤
      (C*((b:ℝ)/b.totient)/(Real.log 2)^2)*(2:ℝ)^k/(k:ℝ)^2 := by
  have hsub : Q.filter (fun q => Nat.clog 2 q=k) ⊆ allShiftedPrimePairs b (2^k) := by
    intro q hq
    obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp,hbp⟩ := hQ q hq
    have hpow := Nat.le_pow_clog (by norm_num : 1 < 2) q
    rw [he] at hpow
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le,hpow⟩,hp,hbp⟩
  have hpow : 2 ≤ 2^k := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hh := hC b hb (2^k) hpow
  push_cast at hh
  rw [Real.log_pow] at hh
  calc
    _ ≤ ((allShiftedPrimePairs b (2^k)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ C*(2:ℝ)^k*((b:ℝ)/b.totient)/((k:ℝ)*Real.log 2)^2 := hh
    _ = _ := by ring

lemma prime_triple_dyadic_count {C : ℝ}
    (hC : ∀ a b : ℕ,0 < a → a < b → ∀ X : ℕ,2 ≤ X →
      ((allPrimeTriples a b X).card:ℝ) ≤ C*X*
        ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log X)^3)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q,q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) (k : ℕ) (hk : 1 ≤ k) :
    ((Q.filter (fun q => Nat.clog 2 q=k)).card:ℝ) ≤
      (C*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log 2)^3)*
        (2:ℝ)^k/(k:ℝ)^3 := by
  have hsub : Q.filter (fun q => Nat.clog 2 q=k) ⊆ allPrimeTriples a b (2^k) := by
    intro q hq
    obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp,hap,hbp⟩ := hQ q hq
    have hpow := Nat.le_pow_clog (by norm_num : 1 < 2) q
    rw [he] at hpow
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le,hpow⟩,hp,hap,hbp⟩
  have hpow : 2 ≤ 2^k := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hh := hC a b ha hab (2^k) hpow
  push_cast at hh
  rw [Real.log_pow] at hh
  calc
    _ ≤ ((allPrimeTriples a b (2^k)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ C*(2:ℝ)^k*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/
      ((k:ℝ)*Real.log 2)^3 := hh
    _ = _ := by ring

theorem prime_pair_reciprocal_tail : ∃ C : ℝ,0 < C ∧
    ∀ (b : ℕ),0 < b → ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
      (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (b*q+1).Prime) →
      (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*((b:ℝ)/b.totient)/Real.log U := by
  obtain ⟨C,hC,hcount⟩ := uniform_prime_pair_bound
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨8*C/Real.log 2,by positivity,?_⟩
  intro b hb Q U hU hQ
  have hh := finite_dyadic_log_square_tail Q hU
    (show 0 ≤ C*((b:ℝ)/b.totient)/(Real.log 2)^2 by positivity)
    (fun q hq => (hQ q hq).1)
    (prime_pair_dyadic_count hcount hb Q (fun q hq => (hQ q hq).2))
  convert hh using 1
  field_simp

theorem prime_triple_reciprocal_tail : ∃ C : ℝ,0 < C ∧
    ∀ (a b : ℕ),0 < a → a < b → ∀ (Q : Finset ℕ) (U : ℝ),1 < U →
      (∀ q ∈ Q,U ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
      (∑ q ∈ Q,(q:ℝ)⁻¹) ≤
        C*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log U)^2 := by
  obtain ⟨C,hC,hcount⟩ := uniform_prime_triple_bound
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨8*C/Real.log 2,by positivity,?_⟩
  intro a b ha hab Q U hU hQ
  have hh := finite_dyadic_log_cube_tail Q hU
    (show 0 ≤ C*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/
      (Real.log 2)^3 by positivity)
    (fun q hq => (hQ q hq).1)
    (prime_triple_dyadic_count hcount ha hab Q (fun q hq => (hQ q hq).2))
  convert hh using 1
  field_simp

end TotientAsymptotic

end

end OAI
