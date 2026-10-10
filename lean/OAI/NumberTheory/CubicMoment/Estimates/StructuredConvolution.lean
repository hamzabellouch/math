import OAI.NumberTheory.CubicMoment.Estimates.PublishedHecke

namespace OAI

/-! Finite ordered prime convolutions used in the exceptional moments.
The weights are independent on the prime factors; the squarefree cutoff
is exposed exactly as the repeated-prime discrepancy. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orderedConvolutionSupport (S : ι → Finset Eisenstein) : Finset Eisenstein :=
  (Fintype.piFinset S).image (fun f => ∏ i, f i)

def orderedConvolution (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (b : Eisenstein) : ℂ :=
  ∑ f ∈ Fintype.piFinset S with (∏ i, f i) = b, ∏ i, w i (f i)

def squarefreeConvolution (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (b : Eisenstein) : ℂ :=
  if Squarefree b then orderedConvolution S w b else 0

/-- Exact collection of the ordered tuples by their product. -/
theorem orderedConvolution_sum (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    (χ : Eisenstein → ℂ) :
    (∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b * χ b) =
      ∑ f ∈ Fintype.piFinset S, (∏ i, w i (f i))*χ (∏ i, f i) := by
  unfold orderedConvolution orderedConvolutionSupport
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b ∈ (Fintype.piFinset S).image (fun f => ∏ i, f i),
        ∑ f ∈ Fintype.piFinset S with (∏ i, f i) = b,
          (∏ i, w i (f i))*χ (∏ i, f i) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image_of_mem _ hf) _

/-- The full independent convolution separates exactly against the primitive
mixed character; no product cutoff is inserted in this identity. -/
theorem orderedConvolution_mixedCubic (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) :
    (∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b * mixedCubic q₁ q₂ b) =
      ∏ i, ∑ p ∈ S i, w i p * mixedCubic q₁ q₂ p := by
  rw [orderedConvolution_sum]
  exact independent_prime_tuple_character_sum S w h₁ h₂

/-- A product of primary primes is squarefree exactly when the tuple has
no repeated prime. The normalization to primary elements makes equality,
rather than association, the correct repetition test. -/
theorem squarefree_prime_tuple_iff (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i)) :
    Squarefree (∏ i, f i) ↔ Function.Injective f := by
  constructor
  · intro hs i j hij
    by_contra hne
    have hdiv : f i*f j ∣ ∏ k, f k := by
      have h := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ f
        (Finset.subset_univ _)
      simpa [hne] using h
    have hs' := hs.squarefree_of_dvd hdiv
    rw [hij] at hs'
    have hu := hs' (f j) (by simp)
    exact (hf j).2.not_isUnit hu
  · intro hi
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      exact (primaryPrimes_isCoprime (hf i) (hf j) (fun h => hij (hi h))).isRelPrime
    · intro i _
      exact (hf i).2.squarefree

/-- The part removed by the squarefree restriction is precisely the sum
of tuples with repeated prime factors. -/
theorem squarefreeConvolution_discrepancy (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein → ℂ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) :
    (∑ b ∈ orderedConvolutionSupport S,
      (orderedConvolution S w b-squarefreeConvolution S w b)*χ b) =
      ∑ f ∈ Fintype.piFinset S with ¬Function.Injective f,
        (∏ i, w i (f i))*χ (∏ i, f i) := by
  have hcollect := orderedConvolution_sum S w
    (fun b => if Squarefree b then 0 else χ b)
  calc
    _ = ∑ b ∈ orderedConvolutionSupport S,
        orderedConvolution S w b*(if Squarefree b then 0 else χ b) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hs : Squarefree b <;> simp [squarefreeConvolution,hs]
    _ = ∑ f ∈ Fintype.piFinset S,
        if Function.Injective f then 0 else (∏ i, w i (f i))*χ (∏ i, f i) := by
      rw [hcollect]
      apply Finset.sum_congr rfl
      intro f hf
      have hprime : ∀ i, primaryPrime (f i) := by
        intro i
        exact hS i (f i) ((Fintype.mem_piFinset.mp hf) i)
      rw [squarefree_prime_tuple_iff f hprime]
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro f hf; split_ifs <;> simp_all

end CubicFirstMoment

end

end OAI
