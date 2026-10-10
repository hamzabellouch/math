import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeQuadraticUniqueness
import OAI.NumberTheory.Ostmann.QuadraticCenter.MaximalQuadraticBias
import OAI.NumberTheory.Ostmann.Characters.NormalizedMixedFourier
import OAI.NumberTheory.Ostmann.Construction.TailFourierMass

namespace OAI

/-! # Both character orders control the actual tail transform -/
namespace Ostmann
open scoped Classical BigOperators

theorem translated_complexJacobi_mean (A : Set ℕ) (N p : ℕ) [NeZero p] (t : ZMod p) :
    translatedResidueCharacterMean A N p (complexJacobiCharacter p) t =
      (residueTestMean (tailSupport A N p) (quadraticResidueTest p (t.val : ℤ)) : ℂ) := by
  have ht : ((t.val : ℤ) : ZMod p) = t := by simp
  have he (r : ℕ) : complexJacobiCharacter p ((r : ZMod p) - t) =
      (quadraticResidueTest p (t.val : ℤ) r : ℂ) := by
    rw [quadraticResidueTest_eq_character, ht]
    simp only [complexJacobiCharacter, jacobiCharacter, MulChar.ringHomComp_apply]
    norm_cast
  simp only [translatedResidueCharacterMean, he, residueTestMean,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

theorem translatedResidueCharacterMean_norm_le_higher (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (hχ : χ ^ 2 ≠ 1) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤ higherCharacterBias A N p := by
  unfold higherCharacterBias
  refine le_csSup ?_ (Or.inr ⟨χ, hχ, t, rfl⟩)
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨ψ, _, u, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p ψ u

theorem translated_tail_character_mean_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤
      maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p := by
  by_cases hχ2 : χ ^ 2 = 1
  · rw [prime_quadratic_character_unique hp2 χ hχ hχ2, translated_complexJacobi_mean,
      Complex.norm_real, Real.norm_eq_abs]
    exact (translated_quadratic_bias_le_maximal (tailSupport A N p) p (t.val : ℤ)).trans
      (le_add_of_nonneg_right (higherCharacterBias_nonneg A N p))
  · exact (translatedResidueCharacterMean_norm_le_higher A N p χ hχ2 t).trans
      (le_add_of_nonneg_left (maximalQuadraticBias_nonneg (tailSupport A N p) p))

theorem tailDensityMask_character_mean (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) :
    ((tailDensityMask A N p).card : ℂ)⁻¹ *
      (∑ x ∈ tailDensityMask A N p, χ (x - t)) = translatedResidueCharacterMean A N p χ t := by
  rw [tailDensityMask_card]
  have hi : Set.InjOn (fun r : ℕ => (r : ZMod p)) (tailSupport A N p) := by
    intro r hr s hs he
    have hrp := Finset.mem_range.mp (tailSupport_subset A N p hr)
    have hsp := Finset.mem_range.mp (tailSupport_subset A N p hs)
    have hm := (ZMod.natCast_eq_natCast_iff' r s p).mp he
    simpa only [Nat.mod_eq_of_lt hrp, Nat.mod_eq_of_lt hsp] using hm
  rw [tailDensityMask, Finset.sum_image hi]
  exact (div_eq_inv_mul _ _).symm

theorem tailDensityMask_reverse_character_mean_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖((tailDensityMask A N p).card : ℂ)⁻¹ *
      (∑ x ∈ tailDensityMask A N p, χ⁻¹ (-a - x))‖ ≤
      maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p := by
  have he (x : ZMod p) : χ⁻¹ (-a - x) = χ⁻¹ (-1) * χ⁻¹ (x - (-a)) := by
    rw [← map_mul]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm _ (χ⁻¹ (-1)), mul_assoc,
    tailDensityMask_character_mean, norm_mul]
  have hunit : ‖χ⁻¹ (-1 : ZMod p)‖ = 1 := by
    exact norm_mulChar_unit χ⁻¹ (-1 : (ZMod p)ˣ)
  rw [hunit, one_mul]
  exact translated_tail_character_mean_bound A N p hp2 χ⁻¹ (inv_ne_one.mpr hχ) (-a)

theorem tail_transform_mixed_bound (A : Set ℕ) (N p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p))
    (hhi : residueDensity (tailDensityMask A N p) ≤ 2 / 3) :
    MixedFourierBound (normalizedResidueTransform (tailDensityMask A N p))
      (max (3 / Real.sqrt (p : ℝ))
        (2 * (maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p))) :=
  normalizedResidueTransform_mixedBound _ hlo hhi _
    (tailDensityMask_reverse_character_mean_bound A N p hp2)

end Ostmann

end OAI
