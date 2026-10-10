import Mathlib
import OAI.Analysis.WeakInfiniteness.DetectedSigns

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u

noncomputable section

open scoped CStarAlgebra Topology

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_square_zero_on_norm_slice_of_gap_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ x ∈ D,x*x=0 ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ → π x ≠ 0 := by
  obtain ⟨h,hhD,hh,hhn⟩ := exists_detected_both_signs_on_norm_slice_any hσ hσγ hgap hA hn hpi D hD hb hα hlocal
  let : IsClosed (D : Set A) := hD.1
  have hpD : h⁺ ∈ D := cfcₙ_mem (·⁺ : ℝ → ℝ) hhD
  have hqD : h⁻ ∈ D := cfcₙ_mem (·⁻ : ℝ → ℝ) hhD
  let Q : A → A → Prop := fun p q =>
    p ∈ hereditarySubalgebra h⁺ (CFC.posPart_nonneg h).isSelfAdjoint ∧
    q ∈ hereditarySubalgebra h⁻ (CFC.negPart_nonneg h).isSelfAdjoint
  obtain ⟨F,z,hzD,_,hzc⟩ := exists_selected_finite_coupling_of_gap_any hσ hσγ hgap hA hn hpi
    D hD b hb hα Q (by
      intro H π hπ hπb
      obtain ⟨hpn,hqn⟩ := hhn H π hπb
      obtain ⟨i,hip,hiq,hin⟩ := exists_core_perturbationData hn hpi hπ
        (CFC.posPart_nonneg h) (CFC.negPart_nonneg h) (CFC.posPart_mul_negPart h) hpn hqn
      exact ⟨i,hereditarySubalgebra_le_of_mem hD (CFC.posPart_nonneg h).isSelfAdjoint hpD hip,
        hereditarySubalgebra_le_of_mem hD (CFC.negPart_nonneg h).isSelfAdjoint hqD hiq,⟨hip,hiq⟩,hin⟩)
  refine ⟨h⁺*z*h⁻,hD.2 h⁺ hpD h⁻ hqD z,?_,?_⟩
  · calc
      (h⁺*z*h⁻)*(h⁺*z*h⁻)=(h⁺*z)*(h⁻*h⁺)*(z*h⁻) := by noncomm_ring
      _ = 0 := by rw [CFC.negPart_mul_posPart,mul_zero,zero_mul]
  · intro H π hπb hnz
    obtain ⟨i,_,hin⟩ := hzc H π hπb
    exact hin (image_hereditary_corner_zero π (CFC.posPart_nonneg h).isSelfAdjoint
      (CFC.negPart_nonneg h).isSelfAdjoint i.property.2.2.1 i.property.2.2.2 hnz)

theorem exists_square_zero_on_norm_slice_any
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ x ∈ D,x*x=0 ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ → π x ≠ 0 := by
  obtain ⟨γ,hγ,hgap⟩ := exists_uniform_gap_any
  exact exists_square_zero_on_norm_slice_of_gap_any (σ := γ/2) (by positivity)
    (by linarith) hgap hA hn hpi D hD hb hα hlocal

end

end WeakPureInfiniteness
end

end OAI
