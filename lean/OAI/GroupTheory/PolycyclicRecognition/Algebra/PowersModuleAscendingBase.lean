import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianizationMonoidFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationFiniteDescent
import Mathlib.Algebra.Group.Submonoid.Membership

namespace OAI

/-! # A cyclic submonoid module supplies an ascending base -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q A : Type} [CommGroup Q] [CommGroup A]

def negativePowersParam (t : Q) : Multiplicative ℕ →* Submonoid.powers t⁻¹ :=
  (powersHom Q t⁻¹).codRestrict _ (fun n => ⟨n.toAdd, rfl⟩)

theorem negativePowersParam_surjective (t : Q) :
    Function.Surjective (negativePowersParam t) := by
  intro u
  obtain ⟨n, hn⟩ := u.property
  exact ⟨Multiplicative.ofAdd n, Subtype.ext hn⟩

theorem ascendingBase_of_powersMonoidModule
    (ρ : Representation ℤ Q (Additive A)) (t : Q) (α : MulAut A)
    (hα : ∀ x : A, ρ t (Additive.ofMul x) = Additive.ofMul (α x))
    [Module.Finite ℤ[Submonoid.powers t⁻¹]
      (Representation.asModule (ρ.comp (Submonoid.powers t⁻¹).subtype))] :
    HasFinitelyGeneratedAscendingBase α := by
  let σ : Representation ℤ (Submonoid.powers t⁻¹) (Additive A) :=
    ρ.comp (Submonoid.powers t⁻¹).subtype
  have hi : ρ t⁻¹ = (mulAutIntegralLinear α).symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply (ρ.apply_bijective t).injective
    change ρ t (ρ t⁻¹ x) = ρ t (Additive.ofMul (α.symm x.toMul))
    rw [Representation.self_inv_apply]
    rw [hα, α.apply_symm_apply]
    rfl
  have he : σ.comp (negativePowersParam t) = inverseAutMonoidRepresentation α := by
    apply MonoidHom.ext
    intro n
    apply LinearMap.ext
    intro x
    change ρ ((t⁻¹) ^ n.toAdd) x = ((mulAutIntegralLinear α).symm.toLinearMap ^ n.toAdd) x
    rw [map_pow, hi]
  have hfg := (finite_representation_comp_iff σ (negativePowersParam t)
    (negativePowersParam_surjective t)).mpr
      (inferInstance : Module.Finite ℤ[Submonoid.powers t⁻¹] σ.asModule)
  rw [he] at hfg
  let := hfg
  exact ascendingBase_of_monoidModule_finite α

end PolycyclicRecognition

end

end OAI
