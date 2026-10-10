import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularDualRepresentation
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Pi

namespace OAI

/-! # The regular dual of a finite free group-ring module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularInversion : ℤ[G] ≃ₗ[ℤ] ℤ[G] :=
  MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ (Equiv.inv G)

@[simp] theorem regularInversion_single (g : G) (r : ℤ) :
    regularInversion (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r :=
  MonoidAlgebra.mapDomainLinearEquiv_single (R := ℤ) (S := ℤ) (Equiv.inv G) r g

theorem regularInversion_rightTranslation (g : G) (q : ℤ[G]) :
    regularInversion ((regularRightTranslation g).hom q) =
      (Rep.leftRegular ℤ G).ρ g (regularInversion q) := by
  induction q using MonoidAlgebra.induction_on with
  | of h =>
    rw [MonoidAlgebra.of_apply, regularRightTranslation_single]
    simp only [regularInversion_single, Representation.ofMulAction_single,
      smul_eq_mul, mul_inv_rev, inv_inv]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul r x hx => simp only [map_smul, hx]

def regularDualFreeEquiv (ι : Type) [Finite ι] :
    (regularDual (Rep.free ℤ G ι)).V ≃ₗ[ℤ] (Rep.free ℤ G ι).V :=
  (Rep.freeLiftLEquiv ℤ G ι (Rep.leftRegular ℤ G)).trans
    ((LinearEquiv.piCongrRight fun _ : ι => regularInversion).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ[G] ι).symm)

@[simp] theorem regularDualFreeEquiv_apply (ι : Type) [Finite ι]
    (f : (regularDual (Rep.free ℤ G ι)).V) (j : ι) :
    regularDualFreeEquiv ι f j =
      regularInversion (f.hom (Finsupp.single j (MonoidAlgebra.single 1 1))) := rfl

def regularDualFreeIso (ι : Type) [Finite ι] :
    regularDual (Rep.free ℤ G ι) ≅ Rep.free ℤ G ι :=
  Rep.mkIso (Representation.Equiv.mk (regularDualFreeEquiv ι) (by
    intro g
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro j
    change regularInversion ((regularRightTranslation g).hom
        (f.hom (Finsupp.single j (MonoidAlgebra.single 1 1)))) =
      (Rep.free ℤ G ι).ρ g (regularDualFreeEquiv ι f) j
    rw [regularInversion_rightTranslation]
    simp only [Representation.finsupp_apply, Finsupp.lsum_apply]
    rw [Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single j]
    · simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.single_eq_same]
      rfl
    · intro k hk hkj
      exact Finsupp.single_eq_of_ne hkj.symm
    · intro hj
      simp only [map_zero, Finsupp.zero_apply]))

theorem regularDualFreeIso_inv_single (ι : Type) [Finite ι]
    (x : (Rep.free ℤ G ι).V) (j : ι) (g : G) (r : ℤ) :
    ((regularDualFreeIso ι).inv.hom x).hom
        (Finsupp.single j (MonoidAlgebra.single g r)) =
      r • (Rep.leftRegular ℤ G).ρ g (regularInversion (x j)) := by
  change Representation.freeLift (Rep.leftRegular ℤ G).ρ
      (fun i => regularInversion (x i)) (Finsupp.single j (MonoidAlgebra.single g r)) = _
  exact Representation.freeLift_single_single (Rep.leftRegular ℤ G).ρ j g r _

end PolycyclicRecognition

end

end OAI
