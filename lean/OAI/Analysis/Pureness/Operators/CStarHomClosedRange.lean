import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.Congruence.Hom

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped CStarAlgebra
variable {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]

def starHomClosedKernel (φ : D →⋆ₐ[ℂ] E) : ClosedStarIdeal D where
  ideal := TwoSidedIdeal.ker φ.toRingHom
  star_mem := by
    intro x hx
    rw [TwoSidedIdeal.mem_ker] at hx ⊢
    change φ (star x) = 0
    change φ x = 0 at hx
    rw [map_star, hx, star_zero]
  isClosed := by
    have he : (TwoSidedIdeal.ker φ.toRingHom : Set D) = {x | φ x = 0} :=
      Set.ext (fun x => TwoSidedIdeal.mem_ker _)
    rw [he]
    exact isClosed_eq (map_continuous φ) continuous_const

lemma starHomClosedKernel_mem (φ : D →⋆ₐ[ℂ] E) (x : D) :
    x ∈ (starHomClosedKernel φ).ideal ↔ φ x = 0 := TwoSidedIdeal.mem_ker _

namespace ClosedStarIdeal
variable (J : ClosedStarIdeal D) (φ : D →⋆ₐ[ℂ] E)
variable (hφ : ∀ x, x ∈ J.ideal → φ x = 0)

include hφ in
lemma liftStarHom_rel : J.ideal.ringCon ≤ RingCon.ker φ.toRingHom := by
  intro x y hxy
  change φ x = φ y
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact hφ (x-y) ((J.ideal.rel_iff x y).mp hxy)

def liftStarHom : J.Quotient →⋆ₐ[ℂ] E :=
  { J.ideal.ringCon.liftₐ φ.toAlgHom (J.liftStarHom_rel φ hφ) with
    map_star' := by
      intro x
      obtain ⟨u, rfl⟩ := J.quotientMap_surjective x
      exact map_star φ u }

lemma liftStarHom_map (x : D) :
    J.liftStarHom φ hφ (J.quotientStarHom x) = φ x := rfl

lemma liftStarHom_injective (hker : ∀ x, φ x = 0 → x ∈ J.ideal) :
    Function.Injective (J.liftStarHom φ hφ) := by
  intro x y hxy
  obtain ⟨u, rfl⟩ := J.quotientMap_surjective x
  obtain ⟨v, rfl⟩ := J.quotientMap_surjective y
  apply Quotient.sound
  change J.ideal.ringCon u v
  rw [J.ideal.rel_iff]
  apply hker
  change φ u = φ v at hxy
  rw [map_sub, hxy, sub_self]

lemma liftStarHom_range : Set.range (J.liftStarHom φ hφ) = Set.range φ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := J.quotientMap_surjective y
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨J.quotientMap u, rfl⟩
end ClosedStarIdeal

variable [PartialOrder D] [StarOrderedRing D]

theorem starHom_isClosed_range (φ : D →⋆ₐ[ℂ] E) : IsClosed (Set.range φ) := by
  let J := starHomClosedKernel φ
  have hφ : ∀ x, x ∈ J.ideal → φ x = 0 := fun x h => (starHomClosedKernel_mem φ x).mp h
  have hi := J.liftStarHom_injective φ hφ (fun x h => (starHomClosedKernel_mem φ x).mpr h)
  have hc := (NonUnitalStarAlgHom.isometry (J.liftStarHom φ hφ) hi).isClosedEmbedding.isClosed_range
  rwa [J.liftStarHom_range φ hφ] at hc

theorem starHom_surjective_of_denseRange (φ : D →⋆ₐ[ℂ] E) (hd : DenseRange φ) :
    Function.Surjective φ := by
  intro x
  have hx := hd x
  rw [(starHom_isClosed_range φ).closure_eq] at hx
  exact hx

theorem starHom_exists_lift_norm_lt (φ : D →⋆ₐ[ℂ] E) (hφ : Function.Surjective φ)
    (x : E) {ε : ℝ} (hε : 0 < ε) : ∃ u : D, φ u = x ∧ ‖u‖ < ‖x‖+ε := by
  obtain ⟨v, rfl⟩ := hφ x
  let J := starHomClosedKernel φ
  let L := J.liftStarHom φ (fun x h => (starHomClosedKernel_mem φ x).mp h)
  have hL : Function.Injective L := J.liftStarHom_injective φ _ (fun x h => (starHomClosedKernel_mem φ x).mpr h)
  obtain ⟨u, hu, hn⟩ := J.quotient_norm_lt_rep (J.quotientMap v) hε
  refine ⟨u, congrArg L hu, ?_⟩
  have he : ‖J.quotientMap v‖ = ‖φ v‖ :=
    (NonUnitalStarAlgHom.norm_map L hL (J.quotientMap v)).symm
  rwa [he] at hn
end CuntzPureness

end

end OAI
