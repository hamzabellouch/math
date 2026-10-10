import OAI.NumberTheory.TotientAsymptotic.PrimeDivisorValueCount
import OAI.NumberTheory.TotientAsymptotic.DyadicValueBounds
import OAI.NumberTheory.TotientAsymptotic.NormalPrimeMass
import OAI.NumberTheory.TotientAsymptotic.NormalityInput

namespace OAI

/-! The small-prime half of the exceptional-value count in Ford Lemma 2.8.
The envelope counts residual totient values, independently of fiber sizes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma small_divisor_value_bound {x : ℝ} {d J : ℕ} (hx : 16 ≤ x)
    (hd : 0 < d) (hdx : (d:ℝ)^2 ≤ x) (hJ : x ≤ (2:ℝ)^J) :
    V (x/d) ≤ (8*dyadicTotientEnvelope J*x/Real.log x)*(d:ℝ)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdx' : (d:ℝ) ≤ x/4 := by
    by_contra hh
    have hh' : x/4 < (d:ℝ) := lt_of_not_ge hh
    have hd4 : 4 < (d:ℝ) := by linarith
    nlinarith only [hdx,hh',hd4]
  have ht4 : 4 ≤ x/d := (le_div_iff₀ hd0).mpr (by linarith)
  have htx : x/d ≤ x := (div_le_iff₀ hd0).mpr (by nlinarith only [hd1,hx0])
  have hlog : Real.log x/2 ≤ Real.log (x/d) := by
    have hh := Real.log_le_log (sq_pos_of_pos hd0) hdx
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [Real.log_div hx0.ne' hd0.ne']
    linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  have hb := dyadic_real_value_count_bound ht4 (htx.trans hJ)
  calc
    _ ≤ 4*dyadicTotientEnvelope J*(x/d)/Real.log (x/d) := hb
    _ ≤ 4*dyadicTotientEnvelope J*(x/d)/(Real.log x/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
    _ = _ := by ring

/-- Prime divisors up to the square-root scale, with no choice of preimage
counted more than once. -/
theorem small_prime_value_count {x : ℝ} {J : ℕ} (hx : 16 ≤ x)
    (hJ : x ≤ (2:ℝ)^J) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime ∧ (p:ℝ)^2 ≤ x)
    (hQ : ∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ∈ P) :
    (Q.card:ℝ) ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
      ∑ p ∈ P,((p-1:ℕ):ℝ)⁻¹ := by
  have hb := prime_divisor_value_count x P Q hQ
  have hpbound (p : ℕ) (hp : p ∈ P) :
      V (x/(p-1:ℕ)) ≤ (8*dyadicTotientEnvelope J*x/Real.log x)*((p-1:ℕ):ℝ)⁻¹ := by
    have hprime := (hP p hp).1
    apply small_divisor_value_bound hx (by have := hprime.two_le; omega) _ hJ
    have hs : ((p-1:ℕ):ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2).trans (hP p hp).2
  calc
    _ ≤ 2*∑ p ∈ P,V (x/(p-1:ℕ)) := hb
    _ ≤ 2*∑ p ∈ P,(8*dyadicTotientEnvelope J*x/Real.log x)*((p-1:ℕ):ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpbound) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The exceptional-value bound for small prime factors. -/
theorem small_non_normal_value_count : ∃ C : ℝ,0 < C ∧
    ∀ (S x : ℝ) (N J : ℕ),2 < S → 0 ≤ B S → 4 ≤ N → 16 ≤ x →
    (N:ℝ)^2 ≤ x → x ≤ (2:ℝ)^J → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ p ≤ N ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
      (B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*
        (Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hmass⟩ := non_normal_prime_mass fordLemma26Input
  refine ⟨16*C,by positivity,?_⟩
  intro S x N J hS hBS hN hx hNx hJ Q hQ
  have hP (p : ℕ) (hp : p ∈ nonNormalPrimes S N) : p.Prime ∧ (p:ℝ)^2 ≤ x := by
    have hh := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
    exact ⟨hh.2,(pow_le_pow_left₀ (Nat.cast_nonneg p) (by exact_mod_cast hh.1) 2).trans hNx⟩
  have hb := small_prime_value_count hx hJ (nonNormalPrimes S N) Q hP (by
    intro v hv
    obtain ⟨n,p,hn,hφ,hp,hpn,hv,hle,hnormal⟩ := hQ v hv
    exact ⟨n,p,hn,hφ,hp,hpn,hv,Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle,hp⟩,hnormal⟩⟩)
  have hc : 0 ≤ 16*dyadicTotientEnvelope J*x/Real.log x := by
    have := Real.log_pos (show 1 < x by linarith)
    have := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
    positivity
  calc
    _ ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
        ∑ p ∈ nonNormalPrimes S N,((p-1:ℕ):ℝ)⁻¹ := hb
    _ ≤ (16*dyadicTotientEnvelope J*x/Real.log x)*
        (C*(B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass S hS hBS N hN) hc
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
