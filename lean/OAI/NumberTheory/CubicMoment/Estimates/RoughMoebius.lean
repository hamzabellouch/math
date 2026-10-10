import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleDecomposition
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAuxiliary

namespace OAI

/-! The literal primary-divisor Möbius expansion used in the small-R
branch, and its exact splitting at a prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cutoffMoebius (ψ : ℝ → ℝ) (w : ℝ) (d : Eisenstein) : ℂ :=
  (idealMoebius d:ℂ)*∏ p ∈ primaryPrimeFactors d, (ψ (norm p/w):ℂ)

lemma cutoffMoebius_prime_product (ψ : ℝ → ℝ) (w : ℝ) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) :
    cutoffMoebius ψ w (∏ p ∈ s, p) = ∏ p ∈ s, -(ψ (norm p/w):ℂ) := by
  rw [cutoffMoebius,primaryPrimeFactors_finset_prod s hs,
    idealMoebius_prod_primaryPrimes s hs,Finset.prod_neg]
  push_cast
  rfl

lemma primary_divisors_of_squarefree_eq {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    metaplecticPrimaryDivisors n =
      (primaryPrimeFactors n).powerset.image (fun s => ∏ p ∈ s, p) := by
  let C := metaplecticPrimaryDivisors n
  have hC (c : Eisenstein) (hc : c ∈ C) : primary c ∧ Squarefree c := by
    have hm := Finset.mem_filter.mp hc
    exact ⟨(mem_primaryElementBall.mp hm.1).1,fun x hx => hs x (hx.trans hm.2)⟩
  have hcomplete (c : Eisenstein) (hc : primary c) (_hs : Squarefree c) (hd : c ∣ n) : c ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_primaryElementBall.mpr ⟨hc,norm_le_of_dvd_nonzero (primary_ne_zero hn) hd⟩,hd⟩
  have he := primary_divisors_eq_subset_products C hC hn hcomplete
  have hf : C.filter (· ∣ n) = C := by
    apply Finset.filter_true_of_mem
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  rwa [hf] at he

/-- The small-R expansion is a sum over genuine primary divisors, with
no ordered-factor or unit multiplicity hidden in the coefficient. -/
theorem roughProduct_primary_divisor_sum {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (ψ : ℝ → ℝ) (w : ℝ) :
    (roughProduct ψ w n:ℂ) = ∑ d ∈ metaplecticPrimaryDivisors n, cutoffMoebius ψ w d := by
  rw [primary_divisors_of_squarefree_eq hn hs,
    Finset.sum_image (primaryPrimeFactors_prod_injective
      (fun p hp => (primaryPrimeFactor_spec hn hp).1))]
  rw [roughProduct_moebius_subsets hn]
  push_cast
  apply Finset.sum_congr rfl
  intro s hsP
  rw [cutoffMoebius,primaryPrimeFactors_finset_prod s
    (fun p hp => (primaryPrimeFactor_spec hn (Finset.mem_powerset.mp hsP hp)).1)]

/-- Selecting k factors in the last bin and averaging over all choices
restores the exact Möbius-cutoff coefficient. -/
theorem cutoffMoebius_stopping_bin (ψ : ℝ → ℝ) (w : ℝ)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p)
    (k : ℕ) (hk : k ≤ s.card) :
    (∑ t ∈ s.powersetCard k, (s.card.choose k:ℂ)⁻¹*
      (cutoffMoebius ψ w (∏ p ∈ t, p)*cutoffMoebius ψ w (∏ p ∈ s\t, p))) =
        cutoffMoebius ψ w (∏ p ∈ s, p) := by
  rw [cutoffMoebius_prime_product ψ w s hs]
  calc
    _ = ∑ t ∈ s.powersetCard k, (s.card.choose k:ℂ)⁻¹*
      ((∏ p ∈ t, -(ψ (norm p/w):ℂ))*(∏ p ∈ s\t, -(ψ (norm p/w):ℂ))) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hsub := (Finset.mem_powersetCard.mp ht).1
      rw [cutoffMoebius_prime_product ψ w t (fun p hp => hs p (hsub hp)),
        cutoffMoebius_prime_product ψ w (s\t) (fun p hp => hs p (Finset.mem_sdiff.mp hp).1)]
    _ = _ := stopping_bin_coefficient_identity s k hk (fun p => -(ψ (norm p/w):ℂ))

end CubicFirstMoment

end

end OAI
