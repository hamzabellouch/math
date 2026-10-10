import Mathlib
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools2
import OAI.Analysis.WeakInfiniteness.SquareZero2

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

lemma exists_second_coupling_on_norm_slice
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type 1) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModels B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ U ∈ D,∃ V ∈ D,IsSelfAdjoint U ∧ IsSelfAdjoint V ∧ ∃ ρ : ℝ,0 < ρ ∧
      ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ →
        ∃ p q : A,∃ S T : Set ℝ,
          ContinuouslySupported (U : Unitization ℂ A) (p : Unitization ℂ A) S ∧
          ContinuouslySupported (U : Unitization ℂ A) (q : Unitization ℂ A) T ∧
          (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) ∧ π (p*V*q) ≠ 0 := by
  classical
  obtain ⟨U,hUD,hU,hUc⟩ := exists_first_coupling_on_norm_slice hσ hσγ hgap hA hn hpi D hD hb hα hlocal
  let Q : A → A → Prop := fun p q => ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧
    ContinuouslySupported (U : Unitization ℂ A) (p : Unitization ℂ A) S ∧
    ContinuouslySupported (U : Unitization ℂ A) (q : Unitization ℂ A) T ∧
    (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y)
  obtain ⟨F,V,hVD,hV,hVc⟩ := exists_selected_finite_coupling_of_gap_one hσ hσγ hgap hA hn hpi
    D hD b hb hα Q (by
      intro H π hπ hπb
      obtain ⟨p,hpD,q,_,hp,_,hpq,hpc⟩ := hUc H π hπb
      obtain ⟨u,huD,v,hvD,hu,hv,huv,hun,hvn,S,T,ρ,hρ,huS,hvT,hST⟩ :=
        exists_nonunital_separated_spectral_windows D hD.1 π hU hUD hp.isSelfAdjoint hpD hpq hpc
      obtain ⟨i,hip,hiq,hin⟩ := exists_core_perturbationData hn hpi hπ hu hv huv hun hvn
      refine ⟨i,hereditarySubalgebra_le_of_mem hD hu.isSelfAdjoint huD hip,
        hereditarySubalgebra_le_of_mem hD hv.isSelfAdjoint hvD hiq,?_,hin⟩
      exact ⟨S,T,ρ,hρ,continuouslySupported_hereditary_nonunital U u hu.isSelfAdjoint S huS hip,
        continuouslySupported_hereditary_nonunital U v hv.isSelfAdjoint T hvT hiq,hST⟩)
  let I := {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q}
  choose S T r hr hp hq hsep using fun i : I => i.property.2.2
  have hmin : ∃ ρ : ℝ,0 < ρ ∧ ∀ i ∈ F,ρ ≤ r i := by
    clear hVc
    induction F using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i F _ ih =>
      obtain ⟨ρ,hρ,hρF⟩ := ih
      refine ⟨min (r i) ρ,lt_min (hr i) hρ,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hρF j hj)
  obtain ⟨ρ,hρ,hρF⟩ := hmin
  refine ⟨U,hUD,V,hVD,hU,hV,ρ,hρ,?_⟩
  intro H π hπb
  obtain ⟨i,hi,hin⟩ := hVc H π hπb
  exact ⟨i.val.p,i.val.q,S i,T i,hp i,hq i,
    fun x hx y hy => (hρF i hi).trans (hsep i x hx y hy),hin⟩

end

end WeakPureInfiniteness
end

end OAI
