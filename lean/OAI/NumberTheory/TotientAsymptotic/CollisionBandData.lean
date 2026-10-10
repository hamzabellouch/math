import OAI.NumberTheory.TotientAsymptotic.CommonSquarefreeMass
import OAI.NumberTheory.TotientAsymptotic.DistinctLargestMass

namespace OAI

/-! A single interval's collision data and its left-right symmetry. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

structure CollisionBandConditions {k : ℕ} (a b : ℕ) (i : Fin k)
    (y T U V I : ℝ) (f : PairedFactors k) : Prop where
  product_pos : 0 < pairedProduct f
  product_eq : pairedProduct f=∏ j,f.2 j
  left_two : 2 ≤ f.1 i
  right_two : 2 ≤ f.2 i
  left_lower : T ≤ largestPrimeFactor (f.1 i)
  right_lower : T ≤ largestPrimeFactor (f.2 i)
  left_prime : (a*f.1 i+1).Prime
  right_prime : (b*f.2 i+1).Prime
  different : a*f.1 i+1 ≠ b*f.2 i+1
  left_le : ((a*f.1 i:ℕ):ℝ) ≤ y
  right_le : ((b*f.2 i:ℕ):ℝ) ≤ y
  omega_le : ((pairedProduct f).primeFactorsList.length:ℝ) ≤ I
  support : ∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V
  squarefree : Squarefree (pairedProduct f)

lemma CollisionBandConditions.common {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CollisionBandConditions a b i y T U V I f)
    (he : largestPrimeFactor (f.1 i)=largestPrimeFactor (f.2 i)) :
    CommonLargestConditions a b i y T U V I f :=
  ⟨hf.product_pos,hf.product_eq,hf.left_two,hf.right_two,he,hf.left_lower,
    hf.left_prime,hf.right_prime,hf.different,hf.left_le,hf.right_le,hf.omega_le,hf.support⟩

lemma CollisionBandConditions.distinct {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CollisionBandConditions a b i y T U V I f)
    (hlt : largestPrimeFactor (f.2 i) < largestPrimeFactor (f.1 i)) :
    DistinctLargestConditions a b i y T U V I f :=
  ⟨hf.product_pos,hf.product_eq,hf.left_two,hf.right_two,hlt,hf.left_lower,hf.right_lower,
    hf.left_prime,hf.right_prime,hf.left_le,hf.right_le,hf.omega_le,hf.support⟩

lemma CollisionBandConditions.swap {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CollisionBandConditions a b i y T U V I f) :
    CollisionBandConditions b a i y T U V I f.swap := by
  have he : pairedProduct f.swap=pairedProduct f := hf.product_eq.symm
  refine ⟨?_,hf.product_eq.symm,hf.right_two,hf.left_two,hf.right_lower,hf.left_lower,
    hf.right_prime,hf.left_prime,hf.different.symm,hf.right_le,hf.left_le,?_,?_,?_⟩
  · simpa only [he] using hf.product_pos
  · simpa only [he] using hf.omega_le
  · simpa only [he] using hf.support
  · simpa only [he] using hf.squarefree

lemma collision_swap_sum {k : ℕ} (Q : Finset (PairedFactors k))
    (hQ : ∀ f ∈ Q,pairedProduct f=∏ j,f.2 j) :
    (∑ f ∈ Q.image Prod.swap,(pairedProduct f:ℝ)⁻¹)=∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹ := by
  classical
  rw [Finset.sum_image (fun f _ g _ he => Prod.swap_injective he)]
  apply Finset.sum_congr rfl
  intro f hf
  rw [show pairedProduct f.swap=pairedProduct f from (hQ f hf).symm]

end TotientAsymptotic

end

end OAI
