import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateInverseSections
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedGeneratorSchemes

namespace OAI

/-! # Uniform bounds for the continuous inverse schemes

The finite cover by inverse sections provides common bounds on expanded
word length and on every amplitude, without a measurable-choice premise.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Metric
open scoped BigOperators

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [Fintype I] in
/-- The direct word and the expanded endpoint polynomial agree for an
actual polynomial coordinate group. -/
theorem polynomialWord_generatorScheme_eq {c n : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B)) (X : I → V)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I) (t : Fin n → ℝ) :
    polynomialWord (dynkinProduct a B) X (generatorSchemeWord w i t) =
      polynomialEndpointScheme a w i (B, X) t :=
  (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg).injective
    ((exp_polynomialWord _ hg X _).trans
      (exp_polynomialEndpointScheme a B hB hg X w i t).symm)

/-- Every normalized law has one continuous bounded inverse scheme on a
common ball; its expanded words have common length and amplitude bounds. -/
theorem exists_uniform_bounded_coordinate_inverse {J : Type*} {c : ℕ}
    (a : DynkinCoefficients c 2) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I) (C₀ : ℝ) (n : ℕ) (hdim : finrank ℝ V = n) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ p ∈ normalizedExponentialParameters a w₀ b₀ C₀,
        ∃ (w : Fin n → List (I × ℝ)) (i : Fin n → I)
          (σ : V → Fin n → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : V) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            polynomialWord (dynkinProduct a p.1) p.2 (generatorSchemeWord w i (σ y)) = y := by
  subst n
  classical
  obtain ⟨schemes, ε, hε, hcover⟩ := exists_uniform_coordinate_inverse_sections a b₀ w₀ C₀
  let A (s : (Fin (finrank ℝ V) → List (I × ℝ)) × (Fin (finrank ℝ V) → I)) :=
    Classical.choose (exists_fixed_word_amplitude_bound s.1)
  have hA s : 1 ≤ A s ∧ ∀ j, ∀ z ∈ s.1 j, |z.2| ≤ A s :=
    Classical.choose_spec (exists_fixed_word_amplitude_bound s.1)
  let C := 1 + ∑ s ∈ schemes, A s
  have hAnonneg s : 0 ≤ A s := (by norm_num : (0 : ℝ) ≤ 1).trans (hA s).1
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun s _ => hAnonneg s))
  have hAC s (hs : s ∈ schemes) : A s ≤ C := by
    have hh := Finset.single_le_sum (fun t _ => hAnonneg t) hs
    dsimp [C]
    linarith
  let N := ∑ s ∈ schemes, ∑ j, (2 * (s.1 j).length + 1)
  refine ⟨ε, N, C, hε, hC, ?_⟩
  intro p hp
  obtain ⟨s, hs, σ, hσ, hright⟩ := hcover p hp
  have hBracket := hp.1.1.2.2.1
  have hGroup := hp.1.2
  refine ⟨s.1, s.2, σ, hσ, ?_⟩
  intro y hy
  obtain ⟨he, hnorm⟩ := hright y hy
  refine ⟨hnorm, ?_, ?_, ?_⟩
  · rw [length_generatorSchemeWord]
    exact Finset.single_le_sum
      (f := fun q => ∑ j, (2 * (q.1 j).length + 1)) (fun _ _ => Nat.zero_le _) hs
  · intro z hz
    exact (generatorSchemeWord_amplitude_bound s.1 s.2 (hA s).1 (hA s).2
      (σ y) hnorm.le z hz).trans (hAC s hs)
  · rw [polynomialWord_generatorScheme_eq a p.1 hBracket hGroup]
    exact he

end PolycyclicRecognition

end

end OAI
