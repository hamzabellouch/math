import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.PrimeSamplerCoupling

namespace OAI

/-! # Bounded fresh-word sampling of the complete dependent representation trial -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (R : RepresentationSetup n)

theorem factorExponents_le_n (z : Layout n) (i : Fin 3) : R.factorExponents z i ≤ n := by
  have hs : R.halfSize ≤ n := by
    have hm := R.orderedMixers_card z 0
    have hc := Finset.card_le_univ (R.orderedMixers z 0)
    simp only [Fintype.card_fin] at hc
    omega
  have hf (j : Fin 3) : ⌊R.lowExponent z j⌋₊ ≤ n :=
    Nat.floor_le_of_le ((R.lowExponent_le_halfSize z j).trans (by exact_mod_cast hs))
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  fin_cases i
  · change ⌊R.lowExponent z 2⌋₊ ≤ n
    exact h2
  · change ⌊R.lowExponent z 1⌋₊ - ⌊R.lowExponent z 2⌋₊ ≤ n
    omega
  · change ⌊R.lowExponent z 0⌋₊ - ⌊R.lowExponent z 1⌋₊ ≤ n
    omega

def nestedCoupling (z : Layout n) : SamplerCoupling (R.PrimeSpace z) :=
  triplePrimeCoupling n (R.factorExponents z 0) (R.factorExponents z 1)
    (R.factorExponents z 2)

theorem nestedCoupling_uniform (z : Layout n) :
    (R.nestedCoupling z).idealLaw = FiniteLaw.uniform := triplePrimeCoupling_uniform _ _ _ _

theorem nestedCoupling_failure (z : Layout n) :
    (R.nestedCoupling z).failure ≤ 3 * Real.exp (-((n : ℝ) ^ 2 / 4)) :=
  triplePrimeCoupling_failure (R.factorExponents_le_n z 0)
    (R.factorExponents_le_n z 1) (R.factorExponents_le_n z 2)

def residuesCoupling {z : Layout n} (p : R.PrimeSpace z) : SamplerCoupling (R.Residues p) := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  exact (finCoupling n (prefixModulus p.val 0)).prod
    ((finCoupling n (prefixModulus p.val 1)).prod (finCoupling n (prefixModulus p.val 2)))

theorem residuesCoupling_uniform {z : Layout n} (p : R.PrimeSpace z) :
    (R.residuesCoupling p).idealLaw = FiniteLaw.uniform := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  exact SamplerCoupling.prod_uniform _ _ (finCoupling_uniform _ _)
    (SamplerCoupling.prod_uniform _ _ (finCoupling_uniform _ _) (finCoupling_uniform _ _))

theorem residuesCoupling_failure {z : Layout n} (p : R.PrimeSpace z) :
    (R.residuesCoupling p).failure ≤ 3 / (2 : ℝ) ^ (n ^ 3) := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  have h0 := finCoupling_failure n (prefixModulus p.val 0)
  have h1 := finCoupling_failure n (prefixModulus p.val 1)
  have h2 := finCoupling_failure n (prefixModulus p.val 2)
  have h12 := SamplerCoupling.prod_failure_le
    (finCoupling n (prefixModulus p.val 1)) (finCoupling n (prefixModulus p.val 2))
  have h012 := SamplerCoupling.prod_failure_le
    (finCoupling n (prefixModulus p.val 0))
    ((finCoupling n (prefixModulus p.val 1)).prod (finCoupling n (prefixModulus p.val 2)))
  change ((finCoupling n (prefixModulus p.val 0)).prod
    ((finCoupling n (prefixModulus p.val 1)).prod
      (finCoupling n (prefixModulus p.val 2)))).failure ≤ _
  simp only [div_eq_mul_inv, one_mul] at h0 h1 h2 ⊢
  linarith

def primeHistoryCoupling : SamplerCoupling R.PrimeHistory :=
  R.partitionHistoryCoupling.bind (fun h => R.PrimeSpace h.1.1)
    (fun h => R.nestedCoupling h.1.1)

def trialHistoryCoupling : SamplerCoupling R.TrialHistory :=
  R.primeHistoryCoupling.bind (fun h => R.Residues h.2) (fun h => R.residuesCoupling h.2)

def extraPrimeCoupling (z : Layout n) (hn : 100 ≤ n) :
    SamplerCoupling (R.ExtraPrimeSpace z) := primeCoupling (R.extraPrimeParameter_range z hn).1 n

theorem extraPrimeCoupling_uniform (z : Layout n) (hn : 100 ≤ n) :
    (R.extraPrimeCoupling z hn).idealLaw = R.extraPrimeLaw z hn :=
  primeCoupling_uniform _ _

theorem extraPrimeCoupling_failure (z : Layout n) (hn : 100 ≤ n) :
    (R.extraPrimeCoupling z hn).failure ≤ Real.exp (-((n : ℝ) ^ 2 / 4)) :=
  primeCoupling_failure (R.extraPrimeParameter_range z hn).1 (R.extraPrimeParameter_range z hn).2

def extraHistoryCoupling (hn : 100 ≤ n) : SamplerCoupling R.ExtraTrialHistory :=
  R.trialHistoryCoupling.bind (fun h => R.ExtraPrimeSpace h.1.1.1.1)
    (fun h => R.extraPrimeCoupling h.1.1.1.1 hn)

def bucketHistoryCoupling (hn : 10000 ≤ n) :
    SamplerCoupling (R.BucketTrialHistory (by omega)) :=
  (R.extraHistoryCoupling (by omega)).bind (fun h => R.SeparatorDraws h.1.1 (by omega))
    (fun h => R.separatorCoupling h.1.1 (by omega))

theorem primeHistoryCoupling_uniform : R.primeHistoryCoupling.idealLaw = R.primeLaw := by
  rw [primeHistoryCoupling, SamplerCoupling.bind_idealLaw, R.partitionHistoryCoupling_uniform]
  simp only [R.nestedCoupling_uniform, primeLaw]

theorem trialHistoryCoupling_uniform : R.trialHistoryCoupling.idealLaw = R.trialLaw := by
  rw [trialHistoryCoupling, SamplerCoupling.bind_idealLaw, R.primeHistoryCoupling_uniform]
  simp only [R.residuesCoupling_uniform, trialLaw]

theorem extraHistoryCoupling_uniform (hn : 100 ≤ n) :
    (R.extraHistoryCoupling hn).idealLaw = R.extraTrialLaw hn := by
  rw [extraHistoryCoupling, SamplerCoupling.bind_idealLaw, R.trialHistoryCoupling_uniform]
  simp only [R.extraPrimeCoupling_uniform, extraTrialLaw]

/-- The ideal marginal is the dependent history law, rather than the uniform
law on the final sigma type. -/
theorem bucketHistoryCoupling_uniform (hn : 10000 ≤ n) :
    (R.bucketHistoryCoupling hn).idealLaw = R.bucketTrialLaw hn := by
  rw [bucketHistoryCoupling, SamplerCoupling.bind_idealLaw, R.extraHistoryCoupling_uniform]
  simp only [R.separatorCoupling_uniform, bucketTrialLaw]

def rangeCallBound (_R : RepresentationSetup n) : ℕ :=
  n + 3 * mixerSize n + 6 + 44 * (2 * blockHalf n 0) * 2 ^ (2 * blockHalf n 0)

theorem guessHistoryCoupling_failure :
    R.guessHistoryCoupling.failure ≤ (n + 3 : ℕ) / (2 : ℝ) ^ (n ^ 3) := by
  have h := SamplerCoupling.bind_failure_le R.layoutCoupling (fun _ => Guesses n)
    (fun _ => R.guessesCoupling) (3 / (2 : ℝ) ^ (n ^ 3)) (fun _ => R.guessesCoupling_failure)
  change R.guessHistoryCoupling.failure ≤ _ at h
  have h0 := R.layoutCoupling_failure
  push_cast
  simp only [add_mul, div_eq_mul_inv, add_mul] at h0 h ⊢
  linarith

theorem partitionHistoryCoupling_failure :
    R.partitionHistoryCoupling.failure ≤
      (n + 3 + 3 * mixerSize n : ℕ) / (2 : ℝ) ^ (n ^ 3) := by
  have h := SamplerCoupling.bind_failure_le R.guessHistoryCoupling (fun h => R.Partitions h.1)
    (fun h => R.partitionsCoupling h.1) (3 * mixerSize n / (2 : ℝ) ^ (n ^ 3))
    (fun h => R.partitionsCoupling_failure h.1)
  change R.partitionHistoryCoupling.failure ≤ _ at h
  have h0 := R.guessHistoryCoupling_failure
  push_cast at h0 ⊢
  simp only [div_eq_mul_inv, add_mul] at h0 h ⊢
  linarith

/-- Three low-factor prime calls and one extra-prime call; all other calls are
counted explicitly from the actual permutation, guess, residue and family code. -/
theorem bucketHistoryCoupling_failure (hn : 10000 ≤ n) :
    (R.bucketHistoryCoupling hn).failure ≤
      R.rangeCallBound / (2 : ℝ) ^ (n ^ 3) + 4 * Real.exp (-((n : ℝ) ^ 2 / 4)) := by
  let δ := 1 / (2 : ℝ) ^ (n ^ 3)
  let ε := Real.exp (-((n : ℝ) ^ 2 / 4))
  have hp := SamplerCoupling.bind_failure_le R.partitionHistoryCoupling
    (fun h => R.PrimeSpace h.1.1) (fun h => R.nestedCoupling h.1.1) (3 * ε)
    (fun h => R.nestedCoupling_failure h.1.1)
  have hr := SamplerCoupling.bind_failure_le R.primeHistoryCoupling
    (fun h => R.Residues h.2) (fun h => R.residuesCoupling h.2) (3 * δ)
    (fun h => by simpa only [δ, div_eq_mul_inv, one_mul] using R.residuesCoupling_failure h.2)
  have hq := SamplerCoupling.bind_failure_le R.trialHistoryCoupling
    (fun h => R.ExtraPrimeSpace h.1.1.1.1) (fun h => R.extraPrimeCoupling h.1.1.1.1 (by omega))
    ε (fun h => R.extraPrimeCoupling_failure h.1.1.1.1 (by omega))
  have hs := SamplerCoupling.bind_failure_le (R.extraHistoryCoupling (by omega))
    (fun h => R.SeparatorDraws h.1.1 (by omega))
    (fun h => R.separatorCoupling h.1.1 (by omega))
    ((44 * (2 * blockHalf n 0) * 2 ^ (2 * blockHalf n 0) : ℕ) * δ)
    (fun h => by simpa only [δ, div_eq_mul_inv, one_mul] using
      R.separatorCoupling_failure h.1.1 (by omega))
  have h0 := R.partitionHistoryCoupling_failure
  change R.primeHistoryCoupling.failure ≤ _ at hp
  change R.trialHistoryCoupling.failure ≤ _ at hr
  change (R.extraHistoryCoupling (by omega)).failure ≤ _ at hq
  change (R.bucketHistoryCoupling hn).failure ≤ _ at hs
  dsimp only [δ, ε] at *
  simp only [rangeCallBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  push_cast at h0 hs
  simp only [div_eq_mul_inv, one_mul, add_mul] at h0 hp hr hq hs ⊢
  linarith

/-- Any proved ideal event transfers directly, with no conditioning on sampler success. -/
theorem bucketHistoryCoupling_event (hn : 10000 ≤ n)
    (P : R.BucketTrialHistory (by omega) → Prop) :
    (R.bucketTrialLaw hn).probability P -
        (R.rangeCallBound / (2 : ℝ) ^ (n ^ 3) + 4 * Real.exp (-((n : ℝ) ^ 2 / 4))) ≤
      (R.bucketHistoryCoupling hn).boundedLaw.probability
        (fun h => ∃ x, h = some x ∧ P x) := by
  have h := (R.bucketHistoryCoupling hn).event_lower P
  rw [R.bucketHistoryCoupling_uniform hn] at h
  exact (sub_le_sub_left (R.bucketHistoryCoupling_failure hn) _).trans h

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
