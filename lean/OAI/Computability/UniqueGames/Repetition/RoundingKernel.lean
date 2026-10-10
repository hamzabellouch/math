import OAI.Computability.UniqueGames.Repetition.CollisionLemmas
import OAI.Computability.UniqueGames.Repetition.RoundingPaddingLemmas
import OAI.Computability.UniqueGames.Repetition.RoundingThresholdLemmas

namespace OAI

section

/-! The alphabet-independent high-value bound for the actual projection
operator. Positive vectors are determinized, padded, and rounded using proved
finite constructions. No rounding or repetition hypothesis is exposed. -/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

private theorem distribution_nonempty {T : Type*} [Fintype T]
    (μ : FiniteDistribution T) : Nonempty T := by
  by_contra h
  have : IsEmpty T := not_nonempty_iff.mp h
  have hz : (∑ t, μ.weight t) = 0 := by simp
  linarith [μ.normalized]

/-- Unit mass form of the Dinur--Steurer positive-vector approximation bound.
The loss is independent of both alphabets and of the auxiliary dimension. -/
theorem vectorEnergy_le_gap_rate [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ 1)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - g) :
    K.vectorEnergy f ≤ 1 - g ^ 2 / 8 := by
  classical
  let : Nonempty Q₂ := distribution_nonempty K.outer
  let : Nonempty Q₁ := distribution_nonempty
    (K.inner (Classical.choice (inferInstance : Nonempty Q₂)))
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · let : IsEmpty Ω := hΩ
    have hzero : K.vectorEnergy f = 0 := by simp [vectorEnergy]
    rw [hzero]
    have hsq : g * g ≤ (1 : ℝ) * 1 := mul_le_mul hg1 hg1 hg0 (by norm_num)
    nlinarith
  · let : Nonempty Ω := hΩ
    obtain ⟨labels, hdet⟩ := K.exists_vectorEnergy_le_singleLabelVector f hf
    have hnonneg := vectorAmplitude_nonnegative f hf
    have hrow : ∀ x, rowSquareMass (vectorAmplitude f) x ≤ 1 := by
      intro x
      rw [rowSquareMass_vectorAmplitude]
      exact hmass x
    rw [K.vectorEnergy_singleLabelVector] at hdet
    by_cases hg : g = 0
    · subst g
      simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
      let fallback : A₁ := Classical.choice inferInstance
      have hpad := pairEnergy_le_padded K.symmetricDistribution symmetricLeft
        symmetricRight K.symmetricAccept labels (vectorAmplitude f) hnonneg fallback
      have hone := pairEnergy_le_one_of_unit_rows K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept
        (paddedLabel labels fallback) (paddedAmplitude (vectorAmplitude f))
        (paddedAmplitude_row (vectorAmplitude f) hrow)
      exact hdet.trans (hpad.trans hone)
    · have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hg)
      have hscore (a : Q₁ → A₁) :
          partialLabelScore K.symmetricDistribution symmetricLeft symmetricRight
            K.symmetricAccept a ≤ 1 - g := by
        unfold partialLabelScore
        rw [K.symmetric_probability_eq_assignmentEnergy]
        exact (K.assignmentEnergy_le_collisionValue a).trans
          (K.collisionValue_le_value.trans hvalue)
      exact hdet.trans (pairEnergy_le_of_labeling_gap K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept labels (vectorAmplitude f)
        hnonneg hrow hgpos hscore)

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

end OAI
