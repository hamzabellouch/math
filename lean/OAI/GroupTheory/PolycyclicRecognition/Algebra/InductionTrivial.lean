import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionCoordinates

namespace OAI

/-! # Inducing the trivial module gives the quotient permutation module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

def inductionTrivialLinearEquiv :
    Rep.ind N.subtype (Rep.trivial k N k) ≃ₗ[k] k[G ⧸ N] :=
  (normalInductionEquiv k N (Rep.trivial k N k)).trans
    ((Finsupp.domLCongr (Equiv.inv (G ⧸ N))).trans (MonoidAlgebra.coeffLinearEquiv k).symm)

@[simp] theorem inductionTrivialLinearEquiv_mk (g : G) (r : k) :
    inductionTrivialLinearEquiv k N
      (IndV.mk N.subtype (Rep.trivial k N k).ρ g r) =
        MonoidAlgebra.single (QuotientGroup.mk' N g)⁻¹ r := by
  change (MonoidAlgebra.coeffLinearEquiv k).symm
    (Finsupp.domLCongr (Equiv.inv (G ⧸ N))
      (inductionCoordinates k N (Rep.trivial k N k) (IndV.mk N.subtype _ g r))) = _
  rw [inductionCoordinates_mk, Rep.trivial_ρ_apply, Finsupp.domLCongr_single]
  rfl

def inductionTrivialEquiv :
    (Rep.ind N.subtype (Rep.trivial k N k)).ρ.Equiv
      (Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N))).ρ :=
  Representation.Equiv.mk (inductionTrivialLinearEquiv k N) fun h => by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro r
    change inductionTrivialLinearEquiv k N
        (Representation.ind N.subtype (Rep.trivial k N k).ρ h (IndV.mk N.subtype _ g r)) =
      Representation.leftRegular k (G ⧸ N) (QuotientGroup.mk' N h)
        (inductionTrivialLinearEquiv k N (IndV.mk N.subtype _ g r))
    rw [Representation.ind_mk, inductionTrivialLinearEquiv_mk, inductionTrivialLinearEquiv_mk]
    simp [map_mul, map_inv, mul_inv_rev]

def inductionTrivialIso :
    Rep.ind N.subtype (Rep.trivial k N k) ≅
      Rep.res (QuotientGroup.mk' N) (Rep.leftRegular k (G ⧸ N)) :=
  Rep.mkIso (inductionTrivialEquiv k N)

end PolycyclicRecognition

end

end OAI
