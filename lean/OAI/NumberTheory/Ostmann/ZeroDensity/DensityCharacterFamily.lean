import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveCharacterCard
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianFubini

namespace OAI

/-! # Grouping the actual primitive characters by their conductors -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def densityCharacterFamily (F : Finset PrimitiveComplexCharacter) (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  ((F.filter fun χ => χ.modulus = q).attach).image fun χ =>
    χ.val.atModulus q (Finset.mem_filter.mp χ.property).2

 theorem densityCharacterFamily_injective (F : Finset PrimitiveComplexCharacter) (q : ℕ) :
    Function.Injective (fun χ : {χ // χ ∈ F.filter (fun χ => χ.modulus = q)} =>
      χ.val.atModulus q (Finset.mem_filter.mp χ.property).2) := by
  intro χ ψ he
  apply Subtype.ext
  have hχ := (Finset.mem_filter.mp χ.property).2
  have hψ := (Finset.mem_filter.mp ψ.property).2
  obtain ⟨⟨m, hm, c, hc, hn⟩, hmem⟩ := χ
  obtain ⟨⟨n, hp, d, hd, hd'⟩, hmem'⟩ := ψ
  dsimp at hχ hψ
  subst m
  subst n
  dsimp [PrimitiveComplexCharacter.atModulus] at he
  cases he
  rfl

 theorem densityCharacterFamily_primitive (F : Finset PrimitiveComplexCharacter) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ∈ densityCharacterFamily F q) : χ.IsPrimitive := by
  obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hχ
  have hψ := (Finset.mem_filter.mp ψ.property).2
  obtain ⟨⟨n, hp, d, hd, hn⟩, hmem⟩ := ψ
  dsimp at hψ
  subst n
  exact hd

 theorem densityCharacterFamily_sum (F : Finset PrimitiveComplexCharacter) (Q : ℕ)
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (f : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    (∑ χ ∈ F, f χ.modulus χ.character) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ densityCharacterFamily F q, f q χ := by
  have hm : ∀ χ ∈ F, χ.modulus ∈ Finset.Icc 1 Q := fun χ hχ =>
    Finset.mem_Icc.mpr ⟨χ.positive, hF χ hχ⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro q _
  rw [densityCharacterFamily, Finset.sum_image]
  · rw [← Finset.sum_attach (F.filter fun χ => χ.modulus = q)]
    apply Finset.sum_congr rfl
    intro χ _
    have hχ := (Finset.mem_filter.mp χ.property).2
    obtain ⟨⟨n, hp, d, hd, hn⟩, hmem⟩ := χ
    dsimp at hχ
    subst n
    rfl
  · exact fun χ _ ψ _ he => densityCharacterFamily_injective F q he

 theorem gaussian_hybrid_primitive_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T, ∫ u : ℝ, densityHalfGaussian u *
        ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ.character (t + u)‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gaussian_hybrid_mean
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T hT a F hF
  rw [densityCharacterFamily_sum F Q hF (fun q χ => ∫ t in Icc (-T) T,
    ∫ u : ℝ, densityHalfGaussian u *
      ‖densityCharacterPolynomial (Finset.Icc 1 N) a χ (t + u)‖ ^ 2)]
  exact hb N Q hQ T hT a (densityCharacterFamily F)
    (fun q _ χ hχ => densityCharacterFamily_primitive F q χ hχ)

end Ostmann

end OAI
