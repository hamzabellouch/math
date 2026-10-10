import OAI.NumberTheory.TotientAsymptotic.OmegaReciprocal
import OAI.NumberTheory.TotientAsymptotic.PrimeDiscardCutoff

namespace OAI

/-! The concrete factor-count moment bounds exceptional shifted primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaExceptionalPrimes (N : ℕ) (T : ℝ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => T ≤ ((p-1).primeFactorsList.length : ℝ))

lemma omega_shifted_prime_mass (N : ℕ) (T : ℝ) :
    (∑ p ∈ omegaExceptionalPrimes N T, ((p-1 : ℕ) : ℝ)⁻¹) ≤
      (3/2 : ℝ)^(-T)*(primeEulerProduct N)^3 := by
  let Q := omegaExceptionalPrimes N T
  have hp (p : ℕ) (h : p ∈ Q) : p.Prime ∧ p ≤ N ∧ T ≤ ((p-1).primeFactorsList.length : ℝ) := by
    obtain ⟨hN,hT⟩ := Finset.mem_filter.mp h
    obtain ⟨hN,hp⟩ := Nat.mem_primesLE.mp hN
    exact ⟨hp,hN,hT⟩
  have hi : Set.InjOn (fun p : ℕ => p-1) (↑Q : Set ℕ) := by
    intro p hP q hQ he
    have h1 := (hp p hP).1.two_le
    have h2 := (hp q hQ).1.two_le
    change p-1=q-1 at he
    omega
  have hh := omega_exceptional_mass (Q.image (fun p => p-1)) (N := N) (T := T) (by
    intro n hn
    obtain ⟨p,hpQ,rfl⟩ := Finset.mem_image.mp hn
    have h := hp p hpQ
    exact ⟨by have := h.1.two_le; omega,(Nat.sub_le p 1).trans h.2.1,h.2.2⟩)
  rw [Finset.sum_image hi] at hh
  exact hh

lemma omega_prime_mass (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 2 ≤ b → ∀ T : ℝ,
      (∑ p ∈ omegaExceptionalPrimes (discardPrimeBound b) T, ((p-1 : ℕ) : ℝ)⁻¹) ≤
        C*Real.exp (6*b-T*Real.log (3/2)) := by
  obtain ⟨D,hD,hM⟩ := hmertens
  refine ⟨D^3*Real.exp 3,by positivity,?_⟩
  intro b hb T
  obtain ⟨hN,_,hB,_⟩ := discardPrimeBound_bounds hb
  have hN1 : (1 : ℝ) < discardPrimeBound b := by exact_mod_cast (show 1 < discardPrimeBound b by omega)
  have hl : Real.log (discardPrimeBound b : ℝ) ≤ Real.exp (2*b+1) := by
    have hh := Real.exp_le_exp.mpr hB
    simpa only [B,Real.exp_log (Real.log_pos hN1)] using hh
  have hp : 0 ≤ primeEulerProduct (discardPrimeBound b) := by
    unfold primeEulerProduct
    apply Finset.prod_nonneg
    intro p hp
    have hpn : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpn
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)

  have he : primeEulerProduct (discardPrimeBound b) ≤ D*Real.exp (2*b+1) :=
    (hM _ (by omega)).trans (mul_le_mul_of_nonneg_left hl hD.le)
  calc
    _ ≤ (3/2 : ℝ)^(-T)*(primeEulerProduct (discardPrimeBound b))^3 := omega_shifted_prime_mass _ _
    _ ≤ (3/2 : ℝ)^(-T)*(D*Real.exp (2*b+1))^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp he _) (Real.rpow_pos_of_pos (by norm_num) _).le
    _ = _ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<3/2),mul_pow,← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = D^3*(Real.exp (Real.log (3/2)*(-T))*Real.exp ((3 : ℝ)*(2*b+1))) := by ring
        _ = _ := by
          rw [← Real.exp_add,mul_assoc,← Real.exp_add]
          congr 2
          ring

end TotientAsymptotic

end

end OAI
