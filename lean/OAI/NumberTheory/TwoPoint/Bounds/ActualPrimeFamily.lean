import OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity

namespace OAI

/-! The prohibited-word data are constructed from the actual prime bands,
not assumed. Padding divisors have the requested degree cap, and the
finite pair catalog can impose any numerical eligibility condition. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def centeredPrimeBands (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (j : Fin J) : Finset ℕ := centeredPrimeSupply E A W j.val

noncomputable def centeredPrimePool (E : Finset ℕ) (A W : ℝ) (J : ℕ) : Finset ℕ :=
  primeTuplePool (centeredPrimeBands E A W J)

lemma centeredPrimeBands_prime (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (j : Fin J) (p : ℕ) (hp : p ∈ centeredPrimeBands E A W J j) : p.Prime :=
  (centeredPrimeSupply_mem hp).1

lemma centeredPrimeBands_disjoint (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (j l : Fin J) (hne : l ≠ j) :
    Disjoint (centeredPrimeBands E A W J j) (centeredPrimeBands E A W J l) :=
  centeredPrimeSupply_pairwise_disjoint E A W hA hW
    (fun he => hne (Fin.ext he.symm))

lemma centeredPrimePool_disjoint_padding (E : Finset ℕ) (A W L : ℝ) (J : ℕ) :
    Disjoint (centeredPrimePool E A W J) (paddingPrimeSupply E L) := by
  apply disjoint_left.mpr
  intro p hp hq
  obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
  exact (disjoint_left.mp (centered_padding_disjoint E A W L j.val)) hj hq

/-- The exclusion set need only contain prime divisors of the fixed shift.
It may contain additional fixed primes, such as those dividing the modulus. -/
noncomputable def actualProhibitedPrimeFamily (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop)
    (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) : ProhibitedPrimeFamily h J M where
  P := centeredPrimePool E A W J
  Q := paddingPrimeSupply E L
  pairs := primeFamilyPairs (centeredPrimeBands E A W J) (paddingPrimeSupply E L) M eligible
  primeP p hp := primeTuplePool_prime (centeredPrimeBands_prime E A W J) hp
  primeQ _ hp := paddingPrimeSupply_prime hp
  disjoint := centeredPrimePool_disjoint_padding E A W L J
  excluded p hp := by
    obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
    intro hph
    have hs := centeredPrimeSupply_mem hj
    exact hs.2.2.1 (hE p hs.1 hph)
  tuple_squarefree dq hdq :=
    (primeTupleDivisors_arithmetic _ (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA hW) (mem_primeFamilyPairs.mp hdq).1).1
  padding_squarefree dq hdq :=
    retainedPrimeDivisor_squarefree _ (fun _ hp => paddingPrimeSupply_prime hp)
      (mem_primeFamilyPairs.mp hdq).2.1
  tuple_card dq hdq :=
    (primeTupleDivisors_arithmetic _ (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA hW) (mem_primeFamilyPairs.mp hdq).1).2.1
  padding_card dq hdq := (mem_primeFamilyPairs.mp hdq).2.2.1
  tuple_pool dq hdq :=
    (primeTupleDivisors_arithmetic _ (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA hW) (mem_primeFamilyPairs.mp hdq).1).2.2
  padding_pool dq hdq :=
    retainedPrimeDivisor_factors _ (fun _ hp => paddingPrimeSupply_prime hp)
      (mem_primeFamilyPairs.mp hdq).2.1

lemma actualProhibitedPrimeFamily_pairs (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ) :
    (d, q) ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs ↔
      d ∈ primeTupleDivisors (centeredPrimeBands E A W J) ∧
        q ∈ retainedPrimeDivisors (paddingPrimeSupply E L) ∧
          q.primeFactors.card ≤ M ∧ eligible d q := mem_primeFamilyPairs

lemma centeredPrimeBand_subset_pool (E : Finset ℕ) (A W : ℝ) (J : ℕ) (j : Fin J) :
    centeredPrimeBands E A W J j ⊆ centeredPrimePool E A W J := by
  intro p hp
  exact mem_primeTuplePool.mpr ⟨j, hp⟩

lemma centeredPrimePool_bounds (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ} (hp : p ∈ centeredPrimePool E A W J) :
    Real.exp A < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp L := by
  obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
  exact centeredPrimeSupply_global_bounds hA hW j.isLt hL hj

lemma paddingPrimeSupply_bounds (E : Finset ℕ) (L : ℝ) {p : ℕ}
    (hp : p ∈ paddingPrimeSupply E L) : (p : ℝ) ≤ Real.exp L :=
  modFivePrimesUpTo_le (Real.exp_pos _).le (Finset.mem_sdiff.mp hp).1

lemma actualProhibitedPrimeFamily_residue_bound (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ}
    (hp : p ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).P ∪
      (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).Q) :
    p ≤ ⌊Real.exp L⌋₊ := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  rcases mem_union.mp hp with hp | hp
  · exact (centeredPrimePool_bounds E A W L J hA hW hL hp).2
  · exact paddingPrimeSupply_bounds E L hp

lemma centeredPrimePool_lower_nat (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ} (hp : p ∈ centeredPrimePool E A W J) : ⌈Real.exp A⌉₊ ≤ p :=
  Nat.ceil_le.mpr (centeredPrimePool_bounds E A W L J hA hW hL hp).1.le

/-- Taking `E = h.primeFactors` is sufficient for any nonzero fixed shift. -/
lemma shiftPrimeFactors_cover {h : ℕ} (hh : h ≠ 0) :
    ∀ p, p.Prime → p ∣ h → p ∈ h.primeFactors :=
  fun _ hp hph => hp.mem_primeFactors hph hh

end TwoPointCorrelations

end OAI
