import OAI.NumberTheory.JointDickman.Counting.BlockPatternTranspose
import OAI.NumberTheory.JointDickman.Counting.ArithmeticCoefficientProbability

namespace OAI

/-! # First-digit pattern averages over the full prime-square period -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem residuePrimePatterns_mean {B M : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) (F : BlockPrimePatterns B M → ℝ) :
    finiteExpectation (primeDigitMass B) (fun r => F (residuePrimePatterns r)) =
      ∑ S : BlockPrimePatterns B M, categoricalProductMass univ
        (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) S * F S := by
  have ht := finiteProductMass_pushforward_test
    (fun (p : auxiliaryPrimes B) (_ : ZMod p.val) => 1/(p.val : ℝ))
    (fun p : auxiliaryPrimes B => blockPrimeHit M p.val) (fun S => (F S : ℂ))
  simp only [blockPrimeHit_pushMass M _ (hsize _ (Subtype.property _))] at ht
  exact_mod_cast ht.symm

theorem arithmeticSquareMean_patterns {B M : ℕ}
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) (F : BlockPrimePatterns B M → ℝ) :
    arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u)) =
      ∑ S : BlockPrimePatterns B M, categoricalProductMass univ
        (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) S * F S := by
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  have hh := prime_square_crt_average B (fun r _ => F (residuePrimePatterns r))
  change arithmeticSquareMean B (fun u => F (residuePrimePatterns (arithmeticFirstDigits B u))) = _ at hh
  simp only [residuePrimePatterns_arithmetic,finiteExpectation_const _ (primeDigitMass_sum B)] at hh
  exact hh.trans (residuePrimePatterns_mean hsize F)

theorem arithmeticSquareMean_pattern_comparison {B M : ℕ}
    (hB : 1 < B) (hM : M ≤ B^2) (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (F : BlockPrimePatterns B M → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ S, |F S| ≤ C*(B : ℝ)^10) :
    |arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u))-
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => F ((blockPatternEquiv B M).symm S))| ≤ 2*C/(B : ℝ) := by
  have hc := block_sites_auxiliary_comparison hB hM F hC hF
  rw [block_sites_crt_mean M (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hsize] at hc
  rw [← arithmeticSquareMean_patterns hsize F] at hc
  have ht := blockPatternEquiv_sum (fun S => F ((blockPatternEquiv B M).symm S))
  simp only [Equiv.symm_apply_apply] at ht
  rwa [ht] at hc

theorem arithmeticSquareMean_add (B : ℕ) (f g : ℕ → ℝ) :
    arithmeticSquareMean B (fun u => f u+g u) = arithmeticSquareMean B f+arithmeticSquareMean B g := by
  simp only [arithmeticSquareMean,sum_add_distrib,add_div]

theorem arithmeticSquareMean_const_mul (B : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    arithmeticSquareMean B (fun u => c*f u) = c*arithmeticSquareMean B f := by
  simp only [arithmeticSquareMean,← mul_sum,mul_div_assoc]

theorem arithmeticSquareMean_mono (B : ℕ) {f g : ℕ → ℝ} (h : ∀ u, f u ≤ g u) :
    arithmeticSquareMean B f ≤ arithmeticSquareMean B g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun u _ => h u)) (by positivity)

end JointDickman

end OAI
