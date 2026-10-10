import OAI.NumberTheory.Ostmann.Quadratic.QuadraticResidueTests

namespace OAI

/-! # Selecting actual oppositely biased endpoint tails -/

namespace Ostmann

open scoped BigOperators Classical

theorem positiveSummandTail_character_sum (A : Set ℕ) (lo hi p : ℕ)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) :
    (∑ n ∈ positiveSummandTail A lo hi, orientedQuadraticValue ε t n p) =
      ε p * ∑ a ∈ summandTail A lo hi, (jacobiSym ((a : ℤ) - t p) p : ℝ) := by
  rw [positiveSummandTail, Finset.sum_image]
  · simp only [orientedQuadraticValue, Finset.mul_sum]
  · intro a ha b hb hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab

theorem negativeSummandTail_character_sum (B : Set ℕ) (lo hi p : ℕ)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) :
    (∑ n ∈ negativeSummandTail B lo hi, orientedQuadraticValue ε t n p) =
      ε p * ∑ b ∈ summandTail B lo hi, (jacobiSym (-(b : ℤ) - t p) p : ℝ) := by
  rw [negativeSummandTail, Finset.sum_image]
  · simp only [orientedQuadraticValue, Finset.mul_sum]
  · intro a ha b hb hab
    exact_mod_cast neg_injective hab

noncomputable def stableTailPrimes (A B : Set ℕ) (N lo hi : ℕ) (P : Finset ℕ) (δ : ℝ) : Finset ℕ :=
  stableBiasPrimes P (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p => residueMass (summandTail A lo hi) (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p)
    (fun p => fiberMass (summandTail B lo hi) (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p)) δ

theorem stable_tail_quadratic_bias {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N lo hi : ℕ) (P : Finset ℕ) (δ E : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, p ≠ 2)
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hlo : ∀ p ∈ P, N + p ≤ lo)
    (hA₀ : (summandTail A lo hi).Nonempty) (hB₀ : (summandTail B lo hi).Nonempty)
    (t : ℕ → ℤ)
    (hbias : ∀ p ∈ P, δ ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p
      (summandTail A lo hi) (summandTail B lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ))
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ))) ≤ E) :
    ∃ ε : ℕ → ℝ,
      (∑ p ∈ P, Real.log (p : ℝ) / p) - 64 * E / δ ^ 2 ≤
        ∑ p ∈ stableTailPrimes A B N lo hi P δ, Real.log (p : ℝ) / p ∧
      ∀ p ∈ stableTailPrimes A B N lo hi P δ,
        (ε p = 1 ∨ ε p = -1) ∧
        (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
        ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 ∧
        (positiveSummandTail A lo hi).card * (δ / 4) ≤
          ∑ n ∈ positiveSummandTail A lo hi, orientedQuadraticValue ε t n p ∧
        (negativeSummandTail B lo hi).card * (δ / 4) ≤
          ∑ n ∈ negativeSummandTail B lo hi, orientedQuadraticValue (fun p => -ε p) t n p := by
  let S := tailSupport A N
  let T := fun p => Finset.range p \ S p
  let μ := fun p => residueMass (summandTail A lo hi) (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p
  let ν := fun p => fiberMass (summandTail B lo hi) (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p)
  have hS : ∀ p ∈ P, (S p).Nonempty := fun p hp => tailSupport_nonempty hA N p (hP p hp).pos
  have hT : ∀ p ∈ P, (T p).Nonempty := fun p hp => tailSupport_complement_nonempty hB (hP p hp).pos (hdis p hp)
  have hcard : ∀ p ∈ P, (S p).card + (T p).card = p := fun p _ => tailSupport_card_add_complement A N p
  have hf : ∀ p ∈ P, ∀ r ∈ S p, |quadraticResidueTest p (t p) r| ≤ 1 :=
    fun p _ r _ => quadraticResidueTest_abs_le p (t p) r
  have hg : ∀ p ∈ P, ∀ r ∈ T p, |quadraticResidueTest p (t p) r| ≤ 1 :=
    fun p _ r _ => quadraticResidueTest_abs_le p (t p) r
  have hsum : ∀ p ∈ P, (∑ r ∈ S p, quadraticResidueTest p (t p) r) +
      (∑ r ∈ T p, quadraticResidueTest p (t p) r) = 0 := by
    intro p hp
    let : Fact p.Prime := ⟨hP p hp⟩
    exact quadraticResidueTest_complement_sum_zero A N p (hodd p hp) (t p)
  obtain ⟨ε, hε⟩ := stable_prime_bias_orientations P S T μ ν
    (fun p => quadraticResidueTest p (t p)) δ hδ hδU hS hT hcard hf hg hsum hbias
  refine ⟨ε, stableBiasPrimes_weight P S T μ ν δ E hδ hP hS hT
    (fun p hp => (hcard p hp).le) hbudget, ?_⟩
  intro p hp
  have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
  let : Fact p.Prime := ⟨hP p hpP⟩
  have hst := stableBiasPrimes_pointwise P S T μ ν
    (fun p => quadraticResidueTest p (t p)) (fun p => quadraticResidueTest p (t p))
    δ hδ.le hδU hS hT hcard hf hg p hp
  have he := hε p hp
  refine ⟨he.1, hst.1, hst.2.1, ?_, ?_⟩
  · have hm : ∀ a ∈ summandTail A lo hi, a % p ∈ S p := by
      intro a ha
      obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
      exact mod_mem_tailSupport (hP p hpP).pos haA (lt_of_le_of_lt (hlo p hpP) halo)
    have hx := he.2.1
    rw [quadratic_positive_projection (summandTail A lo hi) (S p) p (t p) hm,
      ← mul_div_assoc] at hx
    have hc : (0 : ℝ) < (summandTail A lo hi).card := by exact_mod_cast hA₀.card_pos
    rw [positiveSummandTail_card, positiveSummandTail_character_sum]
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hx
  · have hm : ∀ b ∈ summandTail B lo hi, negativeResidue p b ∈ T p := by
      intro b hb
      obtain ⟨hbB, hblo, _⟩ := (mem_summandTail B lo hi b).mp hb
      exact negativeResidue_mem_complement (hP p hpP).pos (hdis p hpP) hbB
        (lt_of_le_of_lt (hlo p hpP) hblo)
    have hx := he.2.2
    rw [quadratic_negative_projection (summandTail B lo hi) (T p) p (t p) hm,
      ← mul_div_assoc] at hx
    have hc : (0 : ℝ) < (summandTail B lo hi).card := by exact_mod_cast hB₀.card_pos
    rw [negativeSummandTail_card, negativeSummandTail_character_sum]
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hx

end Ostmann

end OAI
