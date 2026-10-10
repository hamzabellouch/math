import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.PrimePairSieve

/-- Pushing a finite set through a noninjective map retains the multiplicity
of each image value. In particular, the two ordered Goldbach pairs with
coordinates exchanged must not be identified by the polynomial map. -/
def fiberWeight (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) : ℝ :=
  ((A.filter (fun x => f x = y)).card : ℝ)

lemma fiberWeight_nonneg (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) :
    0 ≤ fiberWeight A f y := by
  exact Nat.cast_nonneg _

lemma sum_fiberWeight_indicator (A : Finset ℕ) (f : ℕ → ℕ)
    (p : ℕ → Prop) [DecidablePred p] :
    (∑ y ∈ A.image f, if p y then fiberWeight A f y else 0) =
      ((A.filter (fun x => p (f x))).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  unfold fiberWeight
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, _, hp⟩
    exact ⟨hx, hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨hx, Finset.mem_image_of_mem f hx, hp⟩

/-- A concrete `BoundingSieve` attached to any polynomial image, with exact
fiber weights rather than an unjustified injectivity assumption. -/
def imageSieve (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) : BoundingSieve where
  support := A.image f
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fiberWeight A f
  weights_nonneg := fiberWeight_nonneg A f
  totalMass := A.card
  nu := ν
  nu_mult := hν
  nu_pos_of_prime := hνpos
  nu_lt_one_of_prime := hνlt

lemma imageSieve_multSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).multSum d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => d ∣ y)

lemma imageSieve_siftedSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) :
    (imageSieve A f P hP ν hν hνpos hνlt).siftedSum =
      ((A.filter (fun x => P.Coprime (f x))).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => P.Coprime y)

/-- First coordinates of the ordered representations of `N` by two primes. -/
def primePairs (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => x.Prime ∧ (N - x).Prime)

/-- The original integer coordinates left after sieving both prime factors. -/
def siftedPairs (N P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => P.Coprime (x * (N - x)))

/-- A prime pair is either sifted or has a coordinate among the prime divisors
of `P`. This is the exact small-prime correction, valid even for `N=0,1`. -/
theorem primePairs_subset (N P : ℕ) (hP : P ≠ 0) :
    primePairs N ⊆ siftedPairs N P ∪
      (P.primeFactors ∪ P.primeFactors.image (fun p => N - p)) := by
  intro x hx
  obtain ⟨hxI, hxprime, hother⟩ := Finset.mem_filter.mp hx
  have hxN : x ≤ N := by
    have := (Finset.mem_Icc.mp hxI).2
    omega
  by_cases hxdvd : x ∣ P
  · exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Nat.mem_primeFactors.mpr ⟨hxprime, hxdvd, hP⟩))
  by_cases hydvd : N - x ∣ P
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨N - x, Nat.mem_primeFactors.mpr ⟨hother, hydvd, hP⟩,
      Nat.sub_sub_self hxN⟩
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  exact ⟨hxI, ((hxprime.coprime_iff_not_dvd.mpr hxdvd).symm).mul_right
    ((hother.coprime_iff_not_dvd.mpr hydvd).symm)⟩

/-- At most twice the number of sieving primes is lost when passing from
ordered prime pairs to sifted polynomial values with multiplicities. -/
theorem card_primePairs_le_sifted (N P : ℕ) (hP : P ≠ 0) :
    (primePairs N).card ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
  calc
    (primePairs N).card ≤
        (siftedPairs N P ∪ (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p))).card :=
      Finset.card_le_card (primePairs_subset N P hP)
    _ ≤ (siftedPairs N P).card + (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p)).card := Finset.card_union_le _ _
    _ ≤ (siftedPairs N P).card +
        (P.primeFactors.card + (P.primeFactors.image (fun p => N - p)).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
      have := Finset.card_image_le (s := P.primeFactors) (f := fun p => N - p)
      omega

/-- The exact polynomial divisor count is the remainder term supplied to the
Selberg sieve; no analytic approximation is built into this model. -/
lemma imageSieve_rem (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).rem d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) - ν d * A.card := by
  rw [BoundingSieve.rem, imageSieve_multSum]
  rfl

/-- A fully concrete prime-pair Λ² bound with ordered-pair multiplicities and
an explicit small-prime correction. The main coefficient and its arithmetic
remainder are still to be estimated by the sieve application. -/
theorem primePairs_lambdaSquared_bound (N P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((primePairs N).card : ℝ) ≤
      ((Finset.Icc 1 (N - 1)).card : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card|) +
      2 * P.primeFactors.card := by
  let s := imageSieve (Finset.Icc 1 (N - 1)) (fun x => x * (N - x))
    P hP ν hν hνpos hνlt
  have hcard : ((primePairs N).card : ℝ) ≤
      ((siftedPairs N P).card : ℝ) + 2 * P.primeFactors.card := by
    exact_mod_cast card_primePairs_le_sifted N P hP.ne_zero
  have hs : s.siftedSum = ((siftedPairs N P).card : ℝ) :=
    imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hb := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w) (BoundingSieve.upperMoebius_lambdaSquared w hw)
  have herr : s.errSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card| := by
    unfold BoundingSieve.errSum
    simp only [s, imageSieve_rem]
    rfl
  rw [hs, herr] at hb
  change ((siftedPairs N P).card : ℝ) ≤
    ((Finset.Icc 1 (N - 1)).card : ℝ) *
      (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) + _ at hb
  linarith

end Problem337.PrimePairSieve

end

end OAI
