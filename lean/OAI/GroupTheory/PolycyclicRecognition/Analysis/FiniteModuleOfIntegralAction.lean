import OAI.GroupTheory.PolycyclicRecognition.Algebra.PointwiseAlgebraicEndomorphism
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

namespace OAI

/-! # A finite module with integral scalar operators is finite over the field -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {K R M : Type} [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [Algebra.FiniteType K R] [Module.Finite R M]

theorem finite_module_of_integral_scalar_action
    (h : ∀ r : R, IsIntegral K (Algebra.lsmul K K M r)) : Module.Finite K M := by
  let φ : R →ₐ[K] Module.End K M := Algebra.lsmul K K M
  let B := φ.range
  let : IsMulCommutative B := .of_setLike_mul_comm (by
    intro b hb c hc
    obtain ⟨r, rfl⟩ := hb
    obtain ⟨s, rfl⟩ := hc
    rw [← map_mul, mul_comm r s, map_mul])
  let : Algebra R B := φ.rangeRestrict.toRingHom.toAlgebra
  let : Module B M := Module.compHom M B.val.toRingHom
  let scalarR : IsScalarTower R B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let scalarK : IsScalarTower K B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Algebra.FiniteType K B :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  let : Algebra.IsIntegral K B := ⟨fun b => by
    apply (isIntegral_algHom_iff B.val Subtype.val_injective).mp
    obtain ⟨r, hr⟩ := b.property
    change IsIntegral K b.val
    rw [← hr]
    exact h r⟩
  let : Module.Finite K B := Algebra.IsIntegral.finite
  let : Module.Finite B M :=
    @Module.Finite.of_restrictScalars_finite R B M _ _ _ _ _ _ scalarR _
  exact @Module.Finite.trans K B M _ _ _ _ _ _ scalarK _ _

end PolycyclicRecognition

end

end OAI
