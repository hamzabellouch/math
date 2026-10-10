import OAI.NumberTheory.TotientAsymptotic.PublishedNormality
import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicHarmonic

namespace OAI

/-! Derive the exceptional reciprocal-prime mass from Ford's count. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma nonNormalPrime_ge_three {S : ℝ} {N p : ℕ} (hS : 1 < S) (hBS : 0 ≤ B S)
    (hp : p ∈ nonNormalPrimes S N) : 3 ≤ p := by
  obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  by_contra hh
  have he : p=2 := by have := hprime.two_le; omega
  subst p
  exact hn (normal_two hS hBS)

lemma dyadic_shift_lower {p : ℕ} (hp : 2 ≤ p) :
    (2 : ℝ)^(Nat.clog 2 p)/4 ≤ ((p-1 : ℕ) : ℝ) := by
  have hd := (dyadic_nat_bounds (by omega : 1 < p)).2.1
  have hsub : ((p-1 : ℕ) : ℝ)+1=p := by exact_mod_cast (show p-1+1=p by omega)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- The only arithmetic input is the literal count in Ford Lemma 2.6.
Dyadic summation supplies its needed reciprocal-weight consequence. -/
theorem non_normal_prime_mass (hford : FordLemma26Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S → 0 ≤ B S → ∀ N : ℕ, 4 ≤ N →
      let L := Nat.clog 2 N
      (∑ p ∈ nonNormalPrimes S N, ((p-1 : ℕ) : ℝ)⁻¹) ≤
        C*(B ((2 : ℝ)^L))^5*(1+Real.log L)*(Real.log S)^(-1/6 : ℝ) := by
  obtain ⟨C,hC,hcount⟩ := hford
  refine ⟨4*C/Real.log 2,by positivity,?_⟩
  intro S hS hBS N hN
  dsimp only
  let L := Nat.clog 2 N
  let Q := nonNormalPrimes S N
  let W := B ((2 : ℝ)^L)
  let E := (Real.log S)^(-1/6 : ℝ)
  let A := C*W^5*E/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 2 ≤ L := by
    have hh := Nat.clog_mono_right 2 hN
    have hc : Nat.clog 2 4=2 := by
      exact Nat.clog_pow 2 2 (by norm_num)
    rw [hc] at hh
    exact hh
  have hW : 0 ≤ W := by
    dsimp [W]
    rw [dyadic_endpoint_B]
    apply Real.log_nonneg
    have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [Real.log_two_gt_d9]
  have hE : 0 ≤ E := Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ S)) _
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (mul_nonneg hC.le (pow_nonneg hW _)) hE) hlog2.le
  have hn : ∀ p ∈ Q, Nat.clog 2 p ∈ Finset.Icc 1 L := by
    intro p hp
    have hp3 := nonNormalPrime_ge_three (by linarith) hBS hp
    refine Finset.mem_Icc.mpr ⟨(dyadic_nat_bounds (by omega : 1 < p)).1,?_⟩
    exact Nat.clog_mono_right 2 ((Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1)
  have hf : ∀ k ∈ Finset.Icc 1 L,
      ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤ A*(2 : ℝ)^k/(k : ℝ) := by
    intro k hk
    by_cases hne : (Q.filter (fun p => Nat.clog 2 p=k)).Nonempty
    · obtain ⟨p,hp⟩ := hne
      obtain ⟨hp,hpk⟩ := Finset.mem_filter.mp hp
      have hp3 := nonNormalPrime_ge_three (by linarith) hBS hp
      have hk2 : 2 ≤ k := by
        have he : 1 < Nat.clog 2 p := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
        omega
      have hsub : Q.filter (fun p => Nat.clog 2 p=k) ⊆ nonNormalPrimes S (2^k) := by
        intro p hp
        obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hnormal⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_,(Nat.mem_primesLE.mp hp).2⟩,hnormal⟩
        simpa only [he] using Nat.le_pow_clog (by norm_num : 1 < 2) p
      have hklarge : 3 < (2 : ℕ)^k := by
        have he := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk2
        norm_num at he ⊢
        omega
      have hb := (show ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤
          (nonNormalPrimes S (2^k)).card by exact_mod_cast Finset.card_le_card hsub).trans
        (hcount S hS (2^k) hklarge)
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hWk : 0 ≤ B ((2 : ℝ)^k) := by
        rw [dyadic_endpoint_B]
        apply Real.log_nonneg
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith [Real.log_two_gt_d9]
      have hWB : B ((2 : ℝ)^k) ≤ W := by
        dsimp [W]
        rw [dyadic_endpoint_B,dyadic_endpoint_B]
        apply Real.log_le_log (mul_pos hkpos hlog2)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hlog2.le
      have hb' : ((Q.filter (fun p => Nat.clog 2 p=k)).card : ℝ) ≤
          C*(2 : ℝ)^k/Real.log ((2 : ℝ)^k)*(B ((2 : ℝ)^k))^5*E := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat,E] using hb
      apply hb'.trans
      calc
        _ ≤ C*(2 : ℝ)^k/Real.log ((2 : ℝ)^k)*W^5*E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hWk hWB 5) (by rw [dyadic_endpoint_log]; positivity)) hE
        _ = _ := by dsimp [A]; rw [dyadic_endpoint_log]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
      positivity
  have he := finite_dyadic_harmonic_mass Q (Nat.clog 2)
    (fun p => ((p-1 : ℕ) : ℝ)) L hA hn
    (fun p hp => dyadic_shift_lower (by have := nonNormalPrime_ge_three (by linarith) hBS hp; omega)) hf
  apply he.trans_eq
  dsimp [A,W,E,L]
  ring

end TotientAsymptotic

end

end OAI
