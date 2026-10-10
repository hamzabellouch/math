import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofFibers

namespace OAI

/-! Finite counting comparison with split rational primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Prime-norm primary elements account for exactly twice the split rational count. -/
lemma primaryPrime_primeNorm_count (X : ℝ) (hX : 0 ≤ X) :
    ((primeCutoff X).filter (fun z => (normNat z).Prime)).card =
      2 * ((Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)).card := by
  let S := (primeCutoff X).filter (fun z => (normNat z).Prime)
  let T := (Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)
  have hmap : (S : Set Eisenstein).MapsTo normNat T := by
    intro z hz
    obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzP,hzX⟩ := mem_primeCutoff.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨?_, hzn⟩, primaryPrime_norm_prime_mod_one hzP hzn⟩
    apply (Nat.le_floor_iff hX).mpr
    rwa [normNat_cast]
  change S.card = 2 * T.card
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ p ∈ T, (S.filter (fun z => normNat z = p)).card) = ∑ _p ∈ T, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpp,hpm⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpX,hpp⟩ := Nat.mem_primesLE.mp hpp
      have he : S.filter (fun z => normNat z = p) =
          (primeCutoff X).filter (fun z => normNat z = p) := by
        ext z
        simp only [S, Finset.mem_filter]
        constructor
        · exact fun h => ⟨h.1.1,h.2⟩
        · exact fun h => ⟨⟨h.1, h.2 ▸ hpp⟩,h.2⟩
      rw [he]
      exact primaryPrime_normFiber_card_eq_two hpp hpm
        ((Nat.le_floor_iff hX).mp hpX)
    _ = 2 * T.card := by simp [mul_comm]

/-- The remaining primary primes have square norm and contribute at most a square-root error. -/
lemma primaryPrime_squareNorm_count_le (X : ℝ) (hX : 0 ≤ X) :
    ((primeCutoff X).filter (fun z => ¬(normNat z).Prime)).card ≤
      2 * (Nat.sqrt ⌊X⌋₊ + 1) := by
  let S := (primeCutoff X).filter (fun z => ¬(normNat z).Prime)
  let T := Finset.range (Nat.sqrt ⌊X⌋₊ + 1)
  have hmap : (S : Set Eisenstein).MapsTo (fun z => Nat.sqrt (normNat z)) T := by
    intro z hz
    obtain ⟨hz,_⟩ := Finset.mem_filter.mp hz
    have hzX : normNat z ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).mpr
      (by rw [normNat_cast]; exact (mem_primeCutoff.mp hz).2)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_sqrt hzX))
  change S.card ≤ 2 * (Nat.sqrt ⌊X⌋₊ + 1)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ p ∈ T, (S.filter (fun z => Nat.sqrt (normNat z) = p)).card) ≤ ∑ _p ∈ T, 2 := by
      apply Finset.sum_le_sum
      intro p _hp
      have hsub : S.filter (fun z => Nat.sqrt (normNat z) = p) ⊆
          (primeCutoff X).filter (fun z => normNat z = p ^ 2) := by
        intro z hz
        obtain ⟨hz,hzp⟩ := Finset.mem_filter.mp hz
        obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
        obtain ⟨q,_hq,hqN⟩ := primaryPrime_norm_square_of_not_prime
          (mem_primeCutoff.mp hz).1 hzn
        have hqp : q = p := by simpa only [hqN, Nat.sqrt_eq'] using hzp
        exact Finset.mem_filter.mpr ⟨hz, by rw [hqN,hqp]⟩
      exact (Finset.card_le_card hsub).trans (primaryPrime_normFiber_card_le_two X (p ^ 2))
    _ = 2 * (Nat.sqrt ⌊X⌋₊ + 1) := by simp [T,mul_comm]

/-- Literal count comparison; no prime ideal theorem is assumed. -/
theorem primaryPrimeCount_comparison (X : ℝ) (hX : 0 ≤ X) :
    let P := ((Nat.primesLE ⌊X⌋₊).filter (fun p => p % 3 = 1)).card
    2 * P ≤ (primeCutoff X).card ∧
      (primeCutoff X).card ≤ 2 * P + 2 * (Nat.sqrt ⌊X⌋₊ + 1) := by
  dsimp only
  have he := Finset.card_filter_add_card_filter_not (s := primeCutoff X)
    (p := fun z => (normNat z).Prime)
  have hmain := primaryPrime_primeNorm_count X hX
  have herr := primaryPrime_squareNorm_count_le X hX
  omega

end CubicFirstMoment

end

end OAI
