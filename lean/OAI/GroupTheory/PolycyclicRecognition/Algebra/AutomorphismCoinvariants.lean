import Mathlib.RepresentationTheory.Coinvariants

namespace OAI

/-! # Coinvariants are unchanged by an automorphism of the acting group -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {k H : Type} [CommRing k] [Group H]

def automorphismCoinvariantsIso (e : H ≃* H) (A : Rep.{0} k H) :
    (Rep.coinvariantsFunctor k H).obj (Rep.res e.toMonoidHom A) ≅
      (Rep.coinvariantsFunctor k H).obj A := by
  let f : Representation.Coinvariants (A.ρ.comp e.toMonoidHom) →ₗ[k]
      Representation.Coinvariants A.ρ :=
    Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _) (by
      intro h
      apply LinearMap.ext
      intro x
      exact Representation.Coinvariants.mk_self_apply A.ρ (e h) x)
  let g : Representation.Coinvariants A.ρ →ₗ[k]
      Representation.Coinvariants (A.ρ.comp e.toMonoidHom) :=
    Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _) (by
      intro h
      apply LinearMap.ext
      intro x
      change Representation.Coinvariants.mk (A.ρ.comp e.toMonoidHom) (A.ρ h x) = _
      have hh := Representation.Coinvariants.mk_self_apply
        (A.ρ.comp e.toMonoidHom) (e.symm h) x
      change Representation.Coinvariants.mk (A.ρ.comp e.toMonoidHom)
        (A.ρ (e (e.symm h)) x) = _ at hh
      simpa only [e.apply_symm_apply] using hh)
  refine LinearEquiv.toModuleIso (LinearEquiv.ofLinearMap f g ?_ ?_)
  · apply Representation.Coinvariants.hom_ext
    rfl
  · apply Representation.Coinvariants.hom_ext
    rfl

@[simp] theorem automorphismCoinvariantsIso_hom_mk (e : H ≃* H) (A : Rep.{0} k H)
    (a : A) :
    (automorphismCoinvariantsIso e A).hom
      (Representation.Coinvariants.mk (A.ρ.comp e.toMonoidHom) a) =
        Representation.Coinvariants.mk A.ρ a := rfl

@[simp] theorem automorphismCoinvariantsIso_inv_mk (e : H ≃* H) (A : Rep.{0} k H)
    (a : A) :
    (automorphismCoinvariantsIso e A).inv (Representation.Coinvariants.mk A.ρ a) =
      Representation.Coinvariants.mk (A.ρ.comp e.toMonoidHom) a := rfl

def automorphismCoinvariantsNatIso (e : H ≃* H) :
    Rep.resFunctor.{0} e.toMonoidHom ⋙ Rep.coinvariantsFunctor k H ≅
      Rep.coinvariantsFunctor k H :=
  NatIso.ofComponents (automorphismCoinvariantsIso e) (by
    intro A B f
    apply ModuleCat.hom_ext
    apply Representation.Coinvariants.hom_ext
    rfl)

end PolycyclicRecognition

end

end OAI
