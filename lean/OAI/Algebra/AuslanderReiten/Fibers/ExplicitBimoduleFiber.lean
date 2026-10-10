import OAI.Algebra.AuslanderReiten.Coordinates.TensorFiniteLift

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "Ae" => R ⊗[k] Rᵐᵒᵖ

abbrev fiberTarget : FiniteLeftModule k Ae := (firstTailModule q).canonicalCosyzygies 4

def normalizedLift : (twistedFiniteModule (sourceTwist q H)).carrier ⟶ (fiberTarget q).carrier :=
  ModuleCat.ofHom (X := (twistedFiniteModule (sourceTwist q H)).carrier)
    (Y := (fiberTarget q).carrier) (((H : k)^2)⁻¹ • finiteLift q H)

@[simp] theorem normalizedLift_apply (x : (twistedFiniteModule (sourceTwist q H)).carrier) :
    normalizedLift q H x = ((H : k)^2)⁻¹ • finiteLift q H x := rfl

abbrev finiteFiber : FiniteLeftModule k Ae :=
  BimoduleFiber.finiteModule (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂)

abbrev explicitBimodule :=
  BimoduleFiber.bimodule (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂)

def rho₁ : (finiteFiber q H₁ H₂).carrier ⟶ (twistedFiniteModule (sourceTwist q H₁)).carrier :=
  FiniteLeftModule.fiberProjection₁
    (twistedFiniteModule (sourceTwist q H₁)) (twistedFiniteModule (sourceTwist q H₂))
    (fiberTarget q) (normalizedLift q H₁) (normalizedLift q H₂)

def rho₂ : (finiteFiber q H₁ H₂).carrier ⟶ (twistedFiniteModule (sourceTwist q H₂)).carrier :=
  FiniteLeftModule.fiberProjection₂
    (twistedFiniteModule (sourceTwist q H₁)) (twistedFiniteModule (sourceTwist q H₂))
    (fiberTarget q) (normalizedLift q H₁) (normalizedLift q H₂)

def explicitFiberSequence :=
  FiniteLeftModule.fiberSequence
    (twistedFiniteModule (sourceTwist q H₁)) (twistedFiniteModule (sourceTwist q H₂))
    (fiberTarget q) (normalizedLift q H₁) (normalizedLift q H₂)

theorem explicitFiberSequence_shortExact : (explicitFiberSequence q H₁ H₂).ShortExact :=
  FiniteLeftModule.fiberSequence_shortExact
    (twistedFiniteModule (sourceTwist q H₁)) (twistedFiniteModule (sourceTwist q H₂))
    (fiberTarget q) (normalizedLift q H₁) (normalizedLift q H₂)

theorem explicitBimodule_finite_k : Module.Finite k (explicitBimodule q H₁ H₂) := by
  infer_instance

theorem explicitBimodule_left :
    Module.Finite R (explicitBimodule q H₁ H₂) ∧
      Module.Projective R (explicitBimodule q H₁ H₂) := by
  let := firstTailModule_left_finite q
  let := firstTailModule_left_projective q
  exact BimoduleFiber.left (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂) (AEnvelopingFrobeniusTrace k q)

theorem explicitBimodule_right :
    Module.Finite Rᵐᵒᵖ (explicitBimodule q H₁ H₂) ∧
      Module.Projective Rᵐᵒᵖ (explicitBimodule q H₁ H₂) := by
  let := firstTailModule_right_finite q
  let := firstTailModule_right_projective q
  exact BimoduleFiber.right (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂) (AEnvelopingFrobeniusTrace k q)

end ArExplicit.T

end

end OAI
