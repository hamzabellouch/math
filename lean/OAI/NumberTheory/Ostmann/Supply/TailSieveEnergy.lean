import OAI.NumberTheory.Ostmann.Supply.IntegerSparseSieve
import OAI.NumberTheory.Ostmann.Construction.TailSieveMasks

namespace OAI

/-! # The sieve budget on the two actual summand tails -/
namespace Ostmann
open scoped Classical BigOperators

theorem tail_sieve_energy_budgets (ls : PublishedAdditiveLargeSieve)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (N lo X Q : ℕ)
    (hdis : ∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q))
    (hlo : N + Q ≤ lo) (hQ : 1 ≤ Q)
    (hAt : (positiveSummandTail A lo X).Nonempty)
    (hBt : (negativeSummandTail B lo X).Nonempty)
    {n m : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (hpQ : ∀ i, p i ≤ Q)
    (hcover : ∀ q, q.Prime → q ≤ Q → ∃ i, p i = q)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (R : ℝ) (hR : 0 < R)
    (hP : (∑ q ∈ Finset.univ.image p,
      |Real.log (((Finset.range q \ tailSupport A N q).card : ℝ) /
        (tailSupport A N q).card)| / q) ≤ R / 16) :
    let S := fun i => tailDensityMask A N (p (e i))
    let α := (Q : ℝ) / 16 * Real.exp (-R)
    let D := (X + 1 : ℝ) + (Q : ℝ) ^ 2
    (α * countingVectorNorm (lowModeVector K
      (averagedCoordinates (positiveSummandTail A lo X)
        (fun x => tensorPointCoordinates (fun i => p (e i)) S
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / (summandTail A lo X).card) ∧
    (α * countingVectorNorm (lowModeVector K
      (averagedCoordinates (negativeSummandTail B lo X)
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => Finset.univ \ S i)
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / (summandTail B lo X).card) := by
  have hp (i : Fin n) : (p i).Prime := Fact.out
  have hk : ∀ q ∈ Finset.univ.image p,
      0 < ((Finset.range q \ tailSupport A N q).card : ℝ) / (tailSupport A N q).card := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    have ht := Finset.card_pos.mpr
      (tailSupport_complement_nonempty hB (hp i).pos (hdis _ (hp i)))
    have hs := Finset.card_pos.mpr (tailSupport_nonempty hA N _ (hp i).pos)
    exact div_pos (by exact_mod_cast ht) (by exact_mod_cast hs)
  have hb := integer_complementary_energy_budgets ls p hc
    (fun i => tailDensityMask A N (p i))
    (fun i => tailDensityMask_nonempty hA N _ (hp i).pos)
    (fun i => tailDensityMask_card_lt hB N _ (hp i).pos (hdis _ (hp i)))
    (fun q => ((Finset.range q \ tailSupport A N q).card : ℝ) / (tailSupport A N q).card)
    hk (fun i => (tailDensityMask_ratio hA N _ (hp i).pos).symm)
    hQ (show 1 ≤ X + 1 by omega) hcover
    (positiveSummandTail A lo X) (negativeSummandTail B lo X) hAt hBt 0 (-(X : ℤ))
    (fun a ha => ?_) (fun b hb => ?_)
    (fun a ha i => positiveSummandTail_mem_mask A N lo X _ (hp i).pos (by have := hpQ i; omega) ha)
    (fun b hb i => negativeSummandTail_mem_mask_complement N lo X _ (hp i).pos
      (hdis _ (hp i)) (by have := hpQ i; omega) hb)
    e K hprod hsmall R hR hP
  · simpa only [positiveSummandTail_card, negativeSummandTail_card, Nat.cast_add,
      Nat.cast_one] using hb
  · have hh := positiveSummandTail_bounds A lo X ha
    push_cast
    omega
  · have hh := negativeSummandTail_bounds B lo X hb
    push_cast
    omega

theorem summandTail_pair_sum (A B : Set ℕ) (lo X : ℕ) (W : ℤ → ℝ) :
    (∑ a ∈ positiveSummandTail A lo X, ∑ b ∈ negativeSummandTail B lo X, W (a - b)) =
      ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X, W ((a + b : ℕ) : ℤ) := by
  unfold positiveSummandTail negativeSummandTail
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      congr 1
      push_cast
      ring
    · intro a ha b hb hab
      exact_mod_cast neg_injective hab
  · intro a ha b hb hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab

end Ostmann

end OAI
