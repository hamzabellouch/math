import OAI.Analysis.KadisonKastler.FiniteStageEmbedding
import OAI.Analysis.KadisonKastler.ExpectedModularRows
import OAI.Analysis.KadisonKastler.MatrixNearCommutant

namespace OAI

/-! # Two-sided matrix preparation of an expected finite subalgebra

The first constructed matrix embedding makes the finite algebra common. The second,
localized matrix embedding aligns its conjugate right algebra without destroying
the first inclusion. All matrix and ordinary-gap losses are calculated
from the actual two unitaries. The expected vector is then proved cyclic
and separating for the corrected neighbor.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixPairPreparationOrder (Q : VonNeumannAlgebra H) :
    PartialOrder (Algebra Q) := CStarAlgebra.spectralOrder _
local instance matrixPairPreparationStarOrder (Q : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra Q) := CStarAlgebra.spectralOrderedRing _

private theorem norm_star_unitary_sub_one (a : unitary (H →L[ℂ] H)) :
    ‖((star a : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(a : H →L[ℂ] H) - 1‖ := by
  simpa only [Unitary.coe_star, star_sub, star_one] using
    norm_star ((a : H →L[ℂ] H) - 1)

/-- Actual two-correction preparation, including the matrix error and
cyclic/separating conclusions needed by the modular spectral theorem.
The trace belongs only to `R`; the vector state on `M` is its composition
with the supplied expectation. -/
theorem exists_matrixPair_preparation
    (hDistance : ∀ Q : VonNeumannAlgebra H,
      PublishedBlockCommutantApproximation (Algebra Q) H)
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (s : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 200000)
    (hgap : kkDistance M N < γ)
    (hMN : MatrixNearInclusion M N γ) (hNM : MatrixNearInclusion N M γ) :
    ∃ a b : unitary (H →L[ℂ] H),
      ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      ‖(b : H →L[ℂ] H) - 1‖ ≤ 45300 * γ ∧
      let N₂ := unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)
      R ≤ N₂ ∧
      conjugateRightAlgebra d.conjugation d.involutive R ≤ N₂.commutant ∧
      MatrixNearInclusion M N₂ (90901 * γ) ∧
      MatrixNearInclusion N₂ M (90901 * γ) ∧
      kkDistance M N₂ < 90902 * γ ∧
      DenseRange (algebraVectorMap N₂ Ω) ∧
      Function.Injective (algebraVectorMap N₂ Ω) ∧
      DenseRange (algebraVectorMap N₂.commutant Ω) ∧
      Function.Injective (algebraVectorMap N₂.commutant Ω) := by
  obtain ⟨hunit, hrightM, hvector⟩ := d.expected_right_data hRM τ P hP hleft hright hΩ
  have : Nontrivial H := by
    refine ⟨⟨Ω, 0, ?_⟩⟩
    intro hz
    rw [hz, norm_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨a, _, hmove, hna⟩ := exists_localized_unitary_matrixUnits_embedding
    s E hmono hR hγ.le (by linarith)
    (nearInclusion_mono_left hRM (nearInclusion_of_kkDistance_lt hgap))
  have hRa := le_unitaryConjugateAlgebra_star a hmove
  have hda := preparedPair_second_correction_gap M N a
  let N₁ := unitaryConjugateAlgebra (star a) N
  have hMN₁ : MatrixNearInclusion M N₁ (169 * γ) :=
    (hMN.conjugate_right (star a)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hN₁M : MatrixNearInclusion N₁ M (169 * γ) :=
    (hNM.conjugate_left (star a)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hd₁ : kkDistance M N₁ < 301 * γ := by
    have hd : kkDistance M N₁ ≤ kkDistance M N + 2 * ‖(a : H →L[ℂ] H) - 1‖ := hda
    linarith
  have hd₁' : kkDistance M.commutant N₁.commutant ≤ 602 * γ := by
    have hd := hMN₁.commutant_kkDistance_le hN₁M (by positivity)
      (hDistance M) (hDistance N₁)
    linarith
  let S := conjugateRightAlgebra d.conjugation d.involutive R
  have hSM : S ≤ M.commutant := by
    rw [← d.commutant]
    exact conjugateRightAlgebra_mono d.conjugation d.involutive hRM
  have hSR : S ≤ R.commutant := commonRightAlgebra_le_commutant M R S hRM
    d.conjugation hrightM (conjugateRightAlgebra_coe d.conjugation d.involutive R)
  have hnear : NearInclusion S N₁.commutant (170 * γ) :=
    nearInclusion_mono_left hSM
      (hN₁M.commutant_nearInclusion (by positivity) (hDistance N₁) (by linarith))
  have hS : S = generatedVonNeumannAlgebra
      (⨆ n, (conjugateMatrixUnits d.conjugation d.involutive (E n)).algebra) := by
    dsimp [S]
    rw [hR]
    exact conjugateRightAlgebra_generated_matrixStages d.conjugation d.involutive s E
  obtain ⟨b, hbLocation, hbMove, hnb⟩ := exists_localized_unitary_matrixUnits_embedding s
    (fun n => conjugateMatrixUnits d.conjugation d.involutive (E n))
    (conjugateMatrixUnits_mono d.conjugation d.involutive s E hmono)
    hS (by positivity : 0 ≤ 170 * γ) (by linarith : 170 * γ ≤ 1 / 1152) hnear
  obtain ⟨hRb, hSb⟩ := preparedPair_second_correction R S N₁ hRa hSR b hbLocation hbMove
  have hdb : kkDistance M (unitaryConjugateAlgebra (star b) N₁) ≤
      kkDistance M N₁ + 300 * (302 * γ) := by
    have hd := preparedPair_second_correction_gap M N₁ b
    linarith
  have hnb' : ‖(b : H →L[ℂ] H) - 1‖ ≤ 45300 * γ := by linarith
  let N₂ := unitaryConjugateAlgebra (star b) N₁
  have hMN₂ : MatrixNearInclusion M N₂ (90901 * γ) :=
    (hMN₁.conjugate_right (star b)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hN₂M : MatrixNearInclusion N₂ M (90901 * γ) :=
    (hN₁M.conjugate_left (star b)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hd₂ : kkDistance M N₂ < 90902 * γ := by
    have hd : kkDistance M N₂ ≤ kkDistance M N₁ + 300 * (302 * γ) := hdb
    linarith
  have hcyclic := expected_modular_corrected_cyclic_separating M N₁ R hRM τ P hP
    hleft hright Ω hΩ d s E hmono hR hirr b hRb hSb
    (by linarith) (by linarith)
  exact ⟨a, b, by linarith, hnb', hRb, hSb, hMN₂, hN₂M, hd₂, hcyclic⟩

end

end KadisonKastler

end OAI
