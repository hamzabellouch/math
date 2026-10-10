import OAI.GroupTheory.PolycyclicRecognition.Analysis.TrivialTensorChains
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneCharacter

namespace OAI

/-! # Rational coefficient representations extending an integral orientation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def rationalCharacterRep (χ : G →* ℚ) : Rep ℤ G :=
  Rep.of ((Algebra.lsmul ℤ ℤ ℚ).toMonoidHom.comp χ)

@[simp] theorem rationalCharacterRep_apply (χ : G →* ℚ) (g : G) (q : ℚ) :
    (rationalCharacterRep χ).ρ g q = χ g * q := rfl

def rationalizedOrientationEquiv {K : Type} [Group K] (R : Rep ℤ K)
    (eR : R.V ≃ₗ[ℤ] ℤ) :
    (trivialTensorCoefficient (ModuleCat.of ℤ ℚ) R).V ≃ₗ[ℤ] ℚ :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) eR).trans (TensorProduct.rid ℤ ℚ)

@[simp] theorem rationalizedOrientationEquiv_tmul {K : Type} [Group K]
    (R : Rep ℤ K) (eR : R.V ≃ₗ[ℤ] ℤ) (q : ℚ) (a : R) :
    rationalizedOrientationEquiv R eR (q ⊗ₜ[ℤ] a) = (eR a : ℚ) * q := by
  change TensorProduct.rid ℤ ℚ (q ⊗ₜ[ℤ] eR a) = _
  rw [TensorProduct.rid_tmul]
  simp only [zsmul_eq_mul]

def rationalizedOrientationIso (N : Subgroup G) (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ)) :
    trivialTensorCoefficient (ModuleCat.of ℤ ℚ) R ≅ Rep.res N.subtype (rationalCharacterRep χ) :=
  Rep.mkIso (Representation.Equiv.mk (rationalizedOrientationEquiv R eR) (by
    intro a
    apply TensorProduct.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro v
    change rationalizedOrientationEquiv R eR
        ((trivialTensorCoefficient (ModuleCat.of ℤ ℚ) R).ρ a (q ⊗ₜ[ℤ] v)) =
      χ (a : G) * rationalizedOrientationEquiv R eR (q ⊗ₜ[ℤ] v)
    rw [trivialTensorCoefficient_tmul, rationalizedOrientationEquiv_tmul,
      rationalizedOrientationEquiv_tmul, hχ, rankOne_action_coordinate]
    push_cast
    dsimp [rankOneCharacter]
    ring))

end PolycyclicRecognition

end

end OAI
