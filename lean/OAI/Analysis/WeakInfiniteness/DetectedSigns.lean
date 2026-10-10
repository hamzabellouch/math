import Mathlib
import OAI.Analysis.WeakInfiniteness.HereditaryDeletion
import OAI.Analysis.WeakInfiniteness.SecondCoupling
import OAI.Analysis.WeakInfiniteness.SquareZero4

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

lemma exists_detected_both_signs_on_norm_slice_any
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    {b : A} (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α)
    (hlocal : NonzeroOnNormSlice D b α) :
    ∃ h ∈ D,IsSelfAdjoint h ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π b‖ →
        π h⁺ ≠ 0 ∧ π h⁻ ≠ 0 := by
  obtain ⟨U,hUD,V,hVD,hU,hV,ρ,hρ,hc⟩ :=
    exists_second_coupling_on_norm_slice_any hσ hσγ hgap hA hn hpi D hD hb hα hlocal
  obtain ⟨h,hhD,hh,m,e,he,hs,hd,hcorners⟩ :=
    exists_hereditary_continuous_deletion D hD.1 U V hUD hVD hU hV hρ
  refine ⟨h,hhD,hh,?_⟩
  intro H π hπb
  obtain ⟨p,q,S,T,hp,hq,hST,hpn⟩ := hc H π hπb
  have hhn : π h ≠ 0 := by
    intro hz
    apply hpn
    rw [← hcorners p q S T hp hq hST,map_mul,map_mul,hz,mul_zero,zero_mul]
  have hhn' : (Unitization.starLift π) (h : Unitization ℂ A) ≠ 0 := by
    rwa [starLift_inr_apply]
  have hsigns := both_signs_in_image_of_partition_diagonals (Unitization.starLift π)
    (hh.map (Unitization.inrNonUnitalStarAlgHom ℂ A)) hhn' e he hs hd
  change ((Unitization.starLift π) (h : Unitization ℂ A))⁺ ≠ 0 ∧
    ((Unitization.starLift π) (h : Unitization ℂ A))⁻ ≠ 0 at hsigns
  rw [starLift_inr_apply] at hsigns
  simpa only [map_posPart π hh,map_negPart π hh] using hsigns

end

end WeakPureInfiniteness
end

end OAI
