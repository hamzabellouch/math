import OAI.NumberTheory.Ostmann.Construction.TypicalTailAssembly
import OAI.NumberTheory.Ostmann.Characters.CharacterMeanRotation

namespace OAI

/-! # The actual tail collision estimate supplies typical character endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def realTranslatedCharacterTest
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (ζ : ℂ)
    (p r : ℕ) : ℝ := (ζ * χ p ((r : ZMod p) - t p)).re

theorem realTranslatedCharacterTest_bound
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (p r : ℕ) :
    |realTranslatedCharacterTest χ t ζ p r| ≤ 1 := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul, hζ, one_mul]
  exact (χ p).norm_le_one _

theorem realTranslatedCharacterTest_mod
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ζ : ℂ) (p r : ℕ) :
    realTranslatedCharacterTest χ t ζ p (r % p) = realTranslatedCharacterTest χ t ζ p r := by
  simp only [realTranslatedCharacterTest, ZMod.natCast_mod]

/-- This is the typical-endpoint step for every prescribed whole shell and
bulk interval. The reference mean is a literal average on the fixed tail. -/
theorem eventual_typical_character_tests {ι : Type*} [DecidableEq ι]
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (J : Finset ι) (α β D δ c : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ L₀ t₀ : ℝ, ∀ L T : ℝ, L₀ ≤ L → t₀ ≤ T →
      Real.log T ≤ β * L + D → ∀ X : ℕ, (X : ℝ) = Real.exp T →
      ∀ (P : Finset ℕ) (R : ι → Finset ℕ)
        (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (ζ : ℂ),
      ‖ζ‖ = 1 → (∀ j ∈ J, R j ⊆ P) →
      (∀ j ∈ J, ∀ p ∈ R j, p.Prime ∧ (p : ℝ) ≤ Real.exp (T / 4) ∧
        Real.exp (α * L) ≤ Real.log (p : ℝ)) →
      (∀ j ∈ J, c ≤ ∑ p ∈ R j, (p : ℝ)⁻¹) →
      (∀ j ∈ J, ∀ p ∈ R j, δ ≤ residueTestMean (tailSupport A N p)
        (realTranslatedCharacterTest χ t ζ p)) →
      ∃ G ⊆ summandTail A (summandTailCutoff T) X,
        a * Real.exp (T / 2) / T ^ 3 ≤ (G.card : ℝ) ∧
        ∀ x ∈ G, ∀ j ∈ J,
          (δ / 2) * (∑ p ∈ R j, (p : ℝ)⁻¹) ≤
            ∑ p ∈ R j, (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - t p)).re ∧
          δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (R j) p : ℂ) * χ p ((x : ZMod p) - t p)‖ := by
  obtain ⟨a, ha, L₀, t₀, ht⟩ := eventual_typical_tail_tests hsize hM hA hB h N hN
    J α β D δ c hα hδ hc
  refine ⟨a, ha, L₀, t₀, ?_⟩
  intro L T hL hT hlog X hX P R χ t ζ hζ hRP hR hmass href
  obtain ⟨G, hG, hcard, hgood⟩ := ht L T hL hT hlog X hX R
    (realTranslatedCharacterTest χ t ζ) hR
    (fun _ _ p _ r _ => realTranslatedCharacterTest_bound χ t ζ hζ p r) hmass (by
      intro j hj
      calc
        δ * (∑ p ∈ R j, (p : ℝ)⁻¹) = ∑ p ∈ R j, (p : ℝ)⁻¹ * δ := by
          rw [← Finset.sum_mul]; exact mul_comm _ _
        _ ≤ _ := Finset.sum_le_sum (fun p hp =>
          mul_le_mul_of_nonneg_left (href j hj p hp) (by positivity)))
  refine ⟨G, hG, hcard, ?_⟩
  intro x hx j hj
  have hg := hgood x hx j hj
  simp_rw [realTranslatedCharacterTest_mod] at hg
  have hp := primeSubsetPrior_mean_positive P (R j) (hRP j hj)
    (hc.trans_le (hmass j hj)) (fun p => ζ * χ p ((x : ZMod p) - t p)) (δ / 2) hg
  exact ⟨hg, (hp.trans (Complex.re_le_norm _)).trans_eq
    (norm_weighted_common_rotation _ _ ζ hζ)⟩

end Ostmann

end OAI
