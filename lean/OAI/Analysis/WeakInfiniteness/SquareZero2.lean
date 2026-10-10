import Mathlib
import OAI.Analysis.WeakInfiniteness.SquareZero

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

open scoped CStarAlgebra Topology

variable {A : Type 1} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_first_coupling_on_norm_slice
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type 1) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModels B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ U ∈ D,IsSelfAdjoint U ∧
      ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ →
        ∃ p ∈ D,∃ q ∈ D,0 ≤ p ∧ 0 ≤ q ∧ p*q=0 ∧ π (p*U*q) ≠ 0 := by
  obtain ⟨F,U,hUD,hU,hUF⟩ := exists_selected_finite_coupling_of_gap_one hσ hσγ hgap hA hn hpi
    D hD b hb hα (fun _ _ => True) (by
      intro H π hπ hπb
      obtain ⟨c,hcD,hc,hcn⟩ := hlocal H π hπ hπb
      obtain ⟨u,huD,v,hvD,hu,hv,huv,hun,hvn⟩ := exists_orthogonal_detected_pair hn hpi π hc hcn
      obtain ⟨F,hFu,hFv,hFn⟩ := exists_core_perturbationData hn hpi hπ hu hv huv hun hvn
      have huD' : u ∈ D := hereditarySubalgebra_le_of_mem hD hc.isSelfAdjoint hcD huD
      have hvD' : v ∈ D := hereditarySubalgebra_le_of_mem hD hc.isSelfAdjoint hcD hvD
      exact ⟨F,hereditarySubalgebra_le_of_mem hD hu.isSelfAdjoint huD' hFu,
        hereditarySubalgebra_le_of_mem hD hv.isSelfAdjoint hvD' hFv,True.intro,hFn⟩)
  refine ⟨U,hUD,hU,?_⟩
  intro H π hπb
  obtain ⟨i,_,hin⟩ := hUF H π hπb
  exact ⟨i.val.p,i.property.1,i.val.q,i.property.2.1,i.val.nonneg_p,i.val.nonneg_q,
    i.val.orthogonal,hin⟩

end

end WeakPureInfiniteness
end

end OAI
