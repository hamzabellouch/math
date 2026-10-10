import OAI.NumberTheory.Ostmann.Construction.TailCoordinateTransport
import OAI.NumberTheory.Ostmann.Construction.PrimeFamilyEnumeration

namespace OAI

/-! # Restrict the full-prime sieve to any indexed sparse prime family -/
namespace Ostmann
open scoped Classical BigOperators

theorem enumerated_tail_sieve_energy_budgets (ls : PublishedAdditiveLargeSieve)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (N lo X Q : ℕ)
    (hdis : ∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q))
    (hcut : N + Q ≤ lo) (hQ : 1 ≤ Q)
    (hAt : (positiveSummandTail A lo X).Nonempty)
    (hBt : (negativeSummandTail B lo X).Nonempty)
    {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (hpQ : ∀ i, p i ≤ Q)
    (K : ℕ)
    (hprod : ∀ T : Finset (Fin n), T.card ≤ K → (∏ i ∈ T, p i) ≤ Q)
    (hsmall : ∀ T : Finset (Fin n), T.card ≤ K →
      (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (R : ℝ) (hR : 0 < R)
    (hP : (∑ q ∈ Nat.primesLE Q,
      |Real.log (((Finset.range q \ tailSupport A N q).card : ℝ) /
        (tailSupport A N q).card)| / q) ≤ R / 16) :
    let S := fun i => tailDensityMask A N (p i)
    let α := (Q : ℝ) / 16 * Real.exp (-R)
    let D := (X + 1 : ℝ) + (Q : ℝ) ^ 2
    let vA := averagedCoordinates (positiveSummandTail A lo X)
      (fun x => tensorPointCoordinates p S (fun i => (x : ZMod (p i))))
    let vB := averagedCoordinates (negativeSummandTail B lo X)
      (fun x => tensorPointCoordinates p (fun i => Finset.univ \ S i)
        (fun i => (x : ZMod (p i))))
    (α * countingVectorNorm (lowModeVector K vA) ^ 2 ≤ D / (summandTail A lo X).card) ∧
    (α * countingVectorNorm (lowModeVector K vB) ^ 2 ≤ D / (summandTail B lo X).card) := by
  let P := Nat.primesLE Q
  let q := primeFamilyEnumeration P
  have hqprime (i : Fin P.card) : (q i).Prime :=
    Nat.prime_of_mem_primesLE (primeFamilyEnumeration_mem P i)
  let (i : Fin P.card) : Fact (q i).Prime := ⟨hqprime i⟩
  have hpmem (i : Fin n) : p i ∈ P := Nat.mem_primesLE.mpr ⟨hpQ i, Fact.out⟩
  let e := finitePrimeFamilyEmbedding P p (prime_family_injective p hc) hpmem
  have he (i : Fin n) : q (e i) = p i :=
    primeFamilyEnumeration_embedding P p (prime_family_injective p hc) hpmem i
  have heprod (T : Finset (Fin n)) (hT : T.card ≤ K) : (∏ i ∈ T, q (e i)) ≤ Q := by
    simpa only [he] using hprod T hT
  have hesmall (T : Finset (Fin n)) (hT : T.card ≤ K) :
      (∑ r ∈ T.image (fun i => q (e i)), (r : ℝ)⁻¹) ≤ 1 / 16 := by
    simpa only [he] using hsmall T hT
  have hPq : (∑ r ∈ Finset.univ.image q,
      |Real.log (((Finset.range r \ tailSupport A N r).card : ℝ) /
        (tailSupport A N r).card)| / r) ≤ R / 16 := by
    simpa only [q, primeFamilyEnumeration_image] using hP
  have hb := tail_sieve_energy_budgets ls hA hB N lo X Q hdis hcut hQ hAt hBt q
    (primeFamilyEnumeration_coprime P (fun r hr => Nat.prime_of_mem_primesLE hr))
    (fun i => Nat.le_of_mem_primesLE (primeFamilyEnumeration_mem P i))
    (fun r hr hle => primeFamilyEnumeration_surjective P r (Nat.mem_primesLE.mpr ⟨hle, hr⟩))
    e K heprod hesmall R hR hPq
  have hpe : (fun i => q (e i)) = p := funext he
  have hea := tail_low_energy_congr (fun i => q (e i)) p hpe A N K (positiveSummandTail A lo X)
  have heb := tail_complement_low_energy_congr (fun i => q (e i)) p hpe A N K (negativeSummandTail B lo X)
  dsimp only at hb
  rw [hea, heb] at hb
  exact hb

end Ostmann

end OAI
