import OAI.Analysis.KadisonKastler.PreparedPairCorrection

namespace OAI

/-! # The localized published amenable embedding

Cameron--Christensen--Sinclair--Smith--White--Wiggins, *Kadison--Kastler
stable factors*, Duke Math. J. 163 (2014), Theorem 3.3(i), printed p.13,
arXiv:1209.4116v3. The unitary belongs to `(P ∪ B)''` and has displacement
at most `150 * γ`. This retains that location, needed for the second
preparation step, and omits the unused pointwise `100 * γ` estimate.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Precisely the inclusion, displacement and localization portions of the
published one-sided embedding theorem. -/
def PublishedLocalizedAmenableEmbedding : Prop :=
  ∀ (P B : VonNeumannAlgebra H) (γ : ℝ), IsInjective P →
    NearInclusion P B γ → γ < 1 / 100 →
    ∃ w : unitary (H →L[ℂ] H),
      (w : H →L[ℂ] H) ∈ generatedVonNeumannAlgebra
        (P.toStarSubalgebra ⊔ B.toStarSubalgebra) ∧
      (∀ x ∈ P, unitaryConj w x ∈ B) ∧ ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * γ

theorem PublishedLocalizedAmenableEmbedding.forget_location
    (h : PublishedLocalizedAmenableEmbedding (H := H)) :
    PublishedAmenableEmbedding (H := H) := by
  intro P B γ hP hnear hγ
  obtain ⟨w, _, hw, hnorm⟩ := h P B γ hP hnear hγ
  exact ⟨w, hw, hnorm⟩

/-- The second published embedding preserves the first common inclusion.
The distance estimate is expressed on the original Hilbert space. -/
theorem exists_prepared_right_correction
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N R S : VonNeumannAlgebra H) (hRN : R ≤ N) (hSR : S ≤ R.commutant)
    (hS : IsInjective S) {γ : ℝ} (hnear : NearInclusion S N.commutant γ)
    (hγ : γ < 1 / 100) :
    ∃ w : unitary (H →L[ℂ] H),
      R ≤ unitaryConjugateAlgebra (star w) N ∧
      S ≤ (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * γ := by
  obtain ⟨w, hw, hmove, hnorm⟩ := hpub S N.commutant γ hS hnear hγ
  obtain ⟨hleft, hright⟩ := preparedPair_second_correction R S N hRN hSR w hw hmove
  refine ⟨w, hleft, hright, hnorm, ?_⟩
  exact (preparedPair_second_correction_gap M N w).trans (by linarith)

end

end KadisonKastler

end OAI
