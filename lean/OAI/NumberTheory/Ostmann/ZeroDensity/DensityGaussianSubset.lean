import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCharacterFamily

namespace OAI

/-! # Gaussian hybrid means on a finite coefficient interval or subset -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_sum_truncate {A : Type*} [AddCommMonoid A]
    (S U : Finset ℕ) (hS : S ⊆ U) (f : ℕ → A) :
    (∑ n ∈ U, if n ∈ S then f n else 0) = ∑ n ∈ S, f n := by
  rw [← Finset.sum_subset hS (fun n _ hn => by simp [hn])]
  exact Finset.sum_congr rfl (fun n hn => by simp [hn])

 theorem gaussian_hybrid_primitive_subset :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → ∀ a : ℕ → ℂ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial S a χ.character (t + u)‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_primitive_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT S hS a F hF
  let b : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have hp (χ : PrimitiveComplexCharacter) (t : ℝ) :
      densityCharacterPolynomial (Finset.Icc 1 N) b χ.character t =
        densityCharacterPolynomial S a χ.character t := by
    unfold densityCharacterPolynomial
    convert density_sum_truncate S (Finset.Icc 1 N) hS
      (fun n => a n * χ.character (n : ZMod χ.modulus) * realAdditivePhase (-(Real.log n * t))) using 1
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ S <;> simp [b, hn]
  have he : (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    convert density_sum_truncate S (Finset.Icc 1 N) hS (fun n => ‖a n‖ ^ 2) using 1
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ S <;> simp [b, hn]
  simpa only [hp, he] using hb N Q hQ T hT b F hF

end Ostmann

end OAI
