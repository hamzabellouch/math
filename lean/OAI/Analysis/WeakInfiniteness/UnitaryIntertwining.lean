import Mathlib
import OAI.Analysis.WeakInfiniteness.IntertwiningConstruction

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

universe u v

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def unitizationInnerFun (u : unitary (Unitization ℂ B)) (b : B) : B :=
  (Unitary.conjStarAlgAut ℂ (Unitization ℂ B) u (b : Unitization ℂ B)).snd

lemma inr_unitizationInnerFun (u : unitary (Unitization ℂ B)) (b : B) :
    ((unitizationInnerFun u b : B) : Unitization ℂ B) =
      Unitary.conjStarAlgAut ℂ (Unitization ℂ B) u (b : Unitization ℂ B) := by
  apply Unitization.ext
  · simp [unitizationInnerFun]
  · rfl

def unitizationInnerHom (u : unitary (Unitization ℂ B)) : B →⋆ₙₐ[ℂ] B where
  toFun := unitizationInnerFun u
  map_zero' := by
    apply Unitization.inr_injective (R := ℂ)
    rw [inr_unitizationInnerFun]
    simp
  map_add' x y := by
    apply Unitization.inr_injective (R := ℂ)
    simp only [inr_unitizationInnerFun,Unitization.inr_add,map_add]
  map_mul' x y := by
    apply Unitization.inr_injective (R := ℂ)
    simp only [inr_unitizationInnerFun,Unitization.inr_mul,map_mul]
  map_smul' c x := by
    apply Unitization.inr_injective (R := ℂ)
    simp only [inr_unitizationInnerFun,Unitization.inr_smul,map_smul,MonoidHom.id_apply]
  map_star' x := by
    apply Unitization.inr_injective (R := ℂ)
    simp only [inr_unitizationInnerFun,Unitization.inr_star,map_star]

lemma unitizationInnerFun_star_left (u : unitary (Unitization ℂ B)) (b : B) :
    unitizationInnerFun (star u) (unitizationInnerFun u b)=b := by
  apply Unitization.inr_injective (R := ℂ)
  rw [inr_unitizationInnerFun,inr_unitizationInnerFun,
    ← Unitary.conjStarAlgAut_symm,StarAlgEquiv.symm_apply_apply]

def unitizationInnerEquiv (u : unitary (Unitization ℂ B)) : B ≃⋆ₐ[ℂ] B :=
  StarAlgEquiv.ofBijective (unitizationInnerHom u)
    ⟨Function.HasLeftInverse.injective ⟨unitizationInnerFun (star u),unitizationInnerFun_star_left u⟩,
      fun b => ⟨unitizationInnerFun (star u) b,by
        change unitizationInnerFun u (unitizationInnerFun (star u) b)=b
        simpa only [star_star] using unitizationInnerFun_star_left (star u) b⟩⟩

def UnitaryFiniteIntertwining (φ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∀ (E : Finset A) (F : Finset B) (ε : ℝ), 0 < ε →
    ∃ u : unitary (Unitization ℂ B),
      (∀ a ∈ E,dist (unitizationInnerFun u (φ a)) (φ a)<ε) ∧
      ∀ b ∈ F,∃ a : A,dist (unitizationInnerFun u (φ a)) b<ε

lemma UnitaryFiniteIntertwining.finiteIntertwining {φ : A →⋆ₙₐ[ℂ] B}
    (h : UnitaryFiniteIntertwining φ) : FiniteIntertwining φ := by
  intro E F ε hε
  obtain ⟨u,hE,hF⟩ := h E F ε hε
  exact ⟨unitizationInnerEquiv u,hE,hF⟩

end

end WeakPureInfiniteness
end

end OAI
