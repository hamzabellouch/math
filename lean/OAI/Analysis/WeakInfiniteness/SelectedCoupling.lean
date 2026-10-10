import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteSelection
import OAI.Analysis.WeakInfiniteness.UniverseCoupling

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

noncomputable section

open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_selected_finite_coupling_of_gap_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    (b : A) (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α) (Q : A → A → Prop)
    (hloc : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → α ≤ ‖π b‖ →
      ∃ F : OrthogonalPerturbationData A n,F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q ∧
        π (positiveCut F.α F.c) ≠ 0) :
    ∃ (F : Finset {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q})
      (U : A),U ∈ D ∧ IsSelfAdjoint U ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π b‖ → ∃ i ∈ F,π (i.val.p*U*i.val.q) ≠ 0 := by
  let I := {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q}
  obtain ⟨F,hF⟩ := finite_norm_support_cover_nonunital
    (fun i : I => positiveCut i.val.α i.val.c) b hb α hα (by
      intro H _ _ _ π hπ hπb
      let H' : ComplexHilbert.{u} := ⟨H⟩
      obtain ⟨i,hiD,hjD,hQ,hin⟩ := hloc H' π hπ hπb
      exact ⟨⟨i,hiD,hjD,hQ⟩,hin⟩)
  obtain ⟨U,hUD,hUsa,ε,hε,hU⟩ := exists_finite_coupling_of_gap_any hσ hσγ hgap hA hn hpi
    D hD (fun i : I => i.val) F (fun i _ => ⟨i.property.1,i.property.2.1⟩)
  refine ⟨F,U,hUD,hUsa,?_⟩
  intro H π hπb
  obtain ⟨i,hi,hin⟩ := hF H π hπb
  have hci := norm_lt_of_positiveCut_image_ne_zero π i.val.nonneg_c i.val.pos_α.le hin
  refine ⟨i,hi,?_⟩
  intro hz
  have he := hU i hi H π hci.le
  rw [hz,norm_zero] at he
  exact (not_le_of_gt hε) he

end

end WeakPureInfiniteness
end

end OAI
