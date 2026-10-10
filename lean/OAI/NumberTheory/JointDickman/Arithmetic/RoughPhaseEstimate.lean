import OAI.NumberTheory.JointDickman.Arithmetic.RoughPrimePresence

namespace OAI

/-! # Explicit oscillatory means for coefficients supported on large primes -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma power_lower_subset_card {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    (D : Finset ℕ) (hD : ∀ p ∈ D, X^c ≤ (p:ℝ))
    (hprod : (∏ p ∈ D, (p:ℝ)) ≤ X) : D.card ≤ ⌈1/c⌉₊ := by
  have hp : (X^c)^D.card ≤ ∏ p ∈ D, (p:ℝ) := by
    calc
      _ = ∏ _p ∈ D, X^c := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (by linarith) _) hD
  have he : X^(c*(D.card:ℝ)) ≤ X^(1:ℝ) := by
    rw [Real.rpow_one]
    rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ X)] at hp
    exact hp.trans hprod
  have hh := (Real.rpow_le_rpow_left_iff hX).mp he
  have hh' : (D.card:ℝ) ≤ 1/c := (le_div_iff₀ hc).mpr (by nlinarith)
  exact_mod_cast hh'.trans (Nat.le_ceil _)

/-- The remaining error is the near-cutoff prime-product mass plus the
explicit repeated-prime exception. All estimates here are unconditional. -/
theorem rough_phase_mean_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Finset ℕ) (F : ℕ → ℂ) (t y Y : ℝ) (N J K : ℕ),
      0 < N → K ≠ 0 → 2 ≤ y → 1 ≤ Y → Y ≤ N →
      (∀ p ∈ P, p.Prime ∧ y < (p:ℝ) ∧ K < p) →
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → p ∉ P → p^k ≤ N → F (p^k) = 1) →
      (∀ D ∈ P.powerset, (∏ p ∈ D, (p:ℝ)) ≤ N → D.card ≤ J) →
      ‖halaszPhaseMean F t N‖/(N:ℝ) ≤
        (2/(1+|t|)+9*(1+|t|)*Y/N)*Real.exp (2*∑ p ∈ P, 1/(p:ℝ))+
        2^J*((Real.log ((N:ℝ)/Y)+C)/Real.log y)*
          (∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h)+2/(K:ℝ) := by
  obtain ⟨C,hC,htail⟩ := primeSubsetTail_bound
  refine ⟨C,hC,?_⟩
  intro P F t y Y N J K hN hK hy hY hYN hP hF1 hFm hFb hlocal hcard
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hp : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hcoef : ∀ p ∈ P, ‖F p‖ ≤ 1 := fun p h => hFb p (hp p h).pos
  have hbounded : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J := by
    intro D hD
    apply hcard D (mem_filter.mp hD).1
    have hh : ((∏ p ∈ D, p : ℕ):ℝ) ≤ N := by exact_mod_cast (mem_filter.mp hD).2
    simpa only [Nat.cast_prod] using hh
  have hpres := primePresence_phase_bound P hp F hcoef t N J (by linarith : 0 ≤ Y) hbounded
  have he := rough_primePresence_phase_error P hp F hF1 hFm hFb t N hlocal
  have hrep := repeatedPrimeExceptions_bound P N hK (fun p h => (hP p h).2.2)
  have htailP := htail P J y Y N hy hY hYN (fun p h => ⟨hp p h,(hP p h).2.1⟩) hcard
  have hm := norm_le_norm_sub_add (halaszPhaseMean F t N)
    (halaszPhaseMean (primePresence P F) t N)
  have hb : ‖halaszPhaseMean F t N‖ ≤
      (2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y)*Real.exp (2*∑ p ∈ P, 1/(p:ℝ))+
      (N:ℝ)*2^J*(((Real.log ((N:ℝ)/Y)+C)/Real.log y)*
        ∑ h ∈ range J, (∑ p ∈ P, 1/(p:ℝ))^h)+2*((N:ℝ)/K) := by
    have htail' := mul_le_mul_of_nonneg_left htailP
      (show 0 ≤ (N:ℝ)*2^J by positivity)
    linarith
  apply (div_le_div_of_nonneg_right hb hNp.le).trans_eq
  field_simp

end JointDickman

end OAI
