import OAI.NumberTheory.CubicMoment.Estimates.SelectedPrimeCanonical
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedRow

namespace OAI

/-! Exact arithmetic after removing the selected largest prime. These
identities retain the original squarefreeness, exclusion and norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_decomposition {d : Eisenstein} (hd : primary d)
    (hs : Squarefree d) (hne : (primaryPrimeFactors d).Nonempty) :
    primaryPrime (largestPrimeChoice d) ∧ primary (largestPrimeRemainder d) ∧
      Squarefree (largestPrimeRemainder d) ∧
      ¬largestPrimeChoice d ∣ largestPrimeRemainder d ∧
      largestPrimeChoice d*largestPrimeRemainder d = d ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors (largestPrimeRemainder d))
        (largestPrimeChoice d) := by
  obtain ⟨p,c,hp,hc,hsc,hpc,he,hl,_⟩ := primary_largest_prime_split hd hs hne
  have hcan := largestPrimeChoice_prime_mul hp hc hsc hpc hl
  rw [he] at hcan
  rw [hcan.1,hcan.2]
  exact ⟨hp,hc,hsc,hpc,he,hl⟩

lemma selectedPrime_product_conditions (r p c e : Eisenstein) (hp : primaryPrime p) :
    (Squarefree (r*(p*c)) ∧ IsCoprime (r*(p*c)) e) ↔
      Squarefree (r*c) ∧ IsCoprime (r*c) e ∧ IsCoprime p (c*(r*e)) := by
  have he : r*(p*c) = p*(r*c) := by ring
  rw [he,squarefree_mul_iff,IsCoprime.mul_left_iff]
  constructor
  · rintro ⟨⟨hpc,_,hsrc⟩,hpe,hrce⟩
    have hpc' : IsCoprime p (r*c) := isRelPrime_iff_isCoprime.mp hpc
    refine ⟨hsrc,hrce,?_⟩
    exact hpc'.of_mul_right_right.mul_right (hpc'.of_mul_right_left.mul_right hpe)
  · rintro ⟨hsrc,hrce,hpcre⟩
    have hpc : IsCoprime p (r*c) :=
      hpcre.of_mul_right_right.of_mul_right_left.mul_right hpcre.of_mul_right_left
    exact ⟨⟨hpc.isRelPrime,hp.2.irreducible.squarefree,hsrc⟩,
      hpcre.of_mul_right_right.of_mul_right_right,hrce⟩

lemma selectedPrime_norm_interval {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0)
    (p : Eisenstein) (a b : ℝ) :
    (a < norm (r*(p*c)) ∧ norm (r*(p*c)) ≤ b) ↔
      a/norm (r*c) < norm p ∧ norm p ≤ b/norm (r*c) := by
  have hn : 0 < norm (r*c) := norm_pos_of_ne_zero (mul_ne_zero hr hc)
  have he : norm (r*(p*c)) = norm p*norm (r*c) := by
    rw [norm_mul_eq,norm_mul_eq,norm_mul_eq]
    ring
  rw [he]
  exact and_congr (div_lt_iff₀ hn).symm (le_div_iff₀ hn).symm

lemma largestPrimePredicate_complement {r c p : Eisenstein}
    (hr : primary r) (hc : primary c)
    (h : largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p) :
    largestPrimePredicate primeTieCode (primaryPrimeFactors c) p := by
  rw [primaryPrimeFactors_mul_union hr hc] at h
  exact fun q hq => h q (Finset.mem_union_right _ hq)

end CubicFirstMoment

end

end OAI
