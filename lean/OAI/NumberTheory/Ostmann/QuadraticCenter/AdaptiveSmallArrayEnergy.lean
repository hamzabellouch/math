import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def adaptiveSmallEuler (L : ℕ) (u : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (L^4+1)).filter Nat.Prime, (1+u/(p:ℝ))

theorem adaptiveSmallEuler_nonneg (L : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ adaptiveSmallEuler L u := by
  unfold adaptiveSmallEuler
  exact Finset.prod_nonneg (fun p hp => by positivity)

theorem adaptiveSmall_harmonic_le (L : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card/(s:ℝ) ≤ adaptiveSmallEuler L u := by
  apply squarefree_weight_sum_le_euler_product _ _
  · exact fun p hp => (Finset.mem_filter.mp hp).2
  · exact fun s hs => (Finset.mem_filter.mp hs).2.1
  · intro s hs p hp
    have hp' := Nat.mem_primeFactors.mp hp
    have hs' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).2
    have hps : p ≤ s := Nat.le_of_dvd (by have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).1; omega) hp'.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp'.1⟩
  · exact hu

theorem positiveDivisorArray_small_energy {L : ℕ} (hL : Squarefree L)
    (q : ℕ) {lam u B : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u) (hB : 0 ≤ B)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (P : ℕ) (R h θ : ℝ)
    (hG : ∀ s ∈ adaptiveSmallSupport L, ∀ d ∈ L.divisors, ∀ v ∈ L.divisors,
      ‖divisorQuadraticSumP d A (mInv d) s v P R h θ‖ ≤ B*Real.sqrt ((2:ℝ)^d.primeFactors.card)) :
    (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*
      ‖positiveDivisorArray L q lam A mInv P R h θ s‖^2) ≤
        (adaptiveSmallEnvelope L lam B)^2*adaptiveSmallEuler L u := by
  calc
    _ ≤ ∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*
        ((adaptiveSmallEnvelope L lam B)^2/(s:ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
      have hs0 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).1
      have he := positiveDivisorArray_small_envelope hL q hlam hB A mInv hs0 P R h θ (hG s hs)
      have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      simpa only [div_pow,Real.sq_sqrt (Nat.cast_nonneg s)] using he2
    _ = (adaptiveSmallEnvelope L lam B)^2 *
        (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card/(s:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (adaptiveSmall_harmonic_le L hu) (sq_nonneg _)

theorem adaptiveSmallArray_energy {L Z : ℕ} (hL : Squarefree L)
    {lam u : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a : AdaptiveArrayParameters}
    (ha : a ∈ adaptiveSmallBaseParameters L Z) :
    (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*‖adaptiveSmallArray L lam A a s‖^2) ≤
      (2*cutoffFourierBound)^2*(1+Real.sqrt 2*lam)^(2*L.primeFactors.card)*
        (reciprocalSqrtDivisorSum L)^2*adaptiveSmallEuler L u := by
  have haR := (Finset.mem_filter.mp ha).2.2
  have hG : ∀ s ∈ adaptiveSmallSupport L, ∀ d ∈ L.divisors, ∀ v ∈ L.divisors,
      ‖divisorQuadraticSumP d A (adaptiveInverse a.modulusResidue d) s v 1
        a.radius a.phaseResidue a.theta‖ ≤ (2*cutoffFourierBound)*Real.sqrt ((2:ℝ)^d.primeFactors.card) := by
    intro s hs d hd v hv
    obtain ⟨hslo,hshi⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1
    exact divisorQuadraticSumP_small_norm_le hL hd hv hslo hshi.le A _ 1 haR _ _
  have he := positiveDivisorArray_small_energy hL a.modulusResidue hlam hu
    (by have := cutoffFourierBound_pos; positivity : 0 ≤ 2*cutoffFourierBound)
    A (adaptiveInverse a.modulusResidue) 1 a.radius a.phaseResidue a.theta hG
  have hsum : (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*‖adaptiveSmallArray L lam A a s‖^2) =
      ∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*
        ‖positiveDivisorArray L a.modulusResidue lam A (adaptiveInverse a.modulusResidue)
          1 a.radius a.phaseResidue a.theta s‖^2 := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [adaptiveSmallArray,ite_eq_left hs]
  rw [hsum]
  convert he using 1
  unfold adaptiveSmallEnvelope
  have hid : (1+Real.sqrt 2*lam)^(2*L.primeFactors.card) =
      ((1+Real.sqrt 2*lam)^L.primeFactors.card)^2 := by
    rw [←pow_mul,Nat.mul_comm]
  rw [hid]
  ring

theorem adaptiveOffEventArray_energy {L Z : ℕ} (hL : Squarefree L)
    {lam u : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u)
    (A : ∀ p : ℕ, Finset (ZMod p)) (K : ℝ) {a : AdaptiveArrayParameters}
    (ha : a ∈ adaptiveOffEventParameters L Z A K) :
    (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*‖adaptiveSmallArray L lam A a s‖^2) ≤
      Real.exp (-(9/5:ℝ)*K)*(1+Real.sqrt 2*lam)^(2*L.primeFactors.card)*
        (reciprocalSqrtDivisorSum L)^2*adaptiveSmallEuler L u := by
  have hG := (Finset.mem_filter.mp ha).2
  have he := positiveDivisorArray_small_energy hL a.modulusResidue hlam hu
    (Real.exp_pos (-(9/10:ℝ)*K)).le A (adaptiveInverse a.modulusResidue)
    1 a.radius a.phaseResidue a.theta (fun s hs d hd v hv => by simpa only [mul_comm] using hG s hs d hd v hv)
  have hsum : (∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*‖adaptiveSmallArray L lam A a s‖^2) =
      ∑ s ∈ adaptiveSmallSupport L,u^s.primeFactors.card*
        ‖positiveDivisorArray L a.modulusResidue lam A (adaptiveInverse a.modulusResidue)
          1 a.radius a.phaseResidue a.theta s‖^2 := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [adaptiveSmallArray,ite_eq_left hs]
  rw [hsum]
  convert he using 1
  unfold adaptiveSmallEnvelope
  rw [mul_pow,mul_pow,←pow_mul,←Real.exp_nat_mul]
  have hex : (2:ℝ)*(-(9/10:ℝ)*K)=-(9/5:ℝ)*K := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hex]
  ring

end Ostmann.QuadraticCenter

end

end OAI
