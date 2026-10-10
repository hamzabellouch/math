import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalQuotientCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FinsuppCohomology
import Mathlib.RepresentationTheory.Rep.Res

namespace OAI

/-! # Restricting the regular representation to a normal subgroup -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

def normalQuotientCoordinatesEquiv : G ≃ (G ⧸ N) × N where
  toFun g := (QuotientGroup.mk' N g, normalQuotientPart N g)
  invFun p := (p.2 : G) * normalQuotientRepresentative N p.1
  left_inv g := normalQuotientPart_decompose N g
  right_inv p := by
    rcases p with ⟨c, n⟩
    apply Prod.ext
    · change QuotientGroup.mk' N ((n : G) * normalQuotientRepresentative N c) = c
      rw [map_mul, normalQuotient_mk_subgroup, one_mul, normalQuotientRepresentative_mk]
    · simp

def restrictedRegularLinearEquiv :
    k[G] ≃ₗ[k] ((G ⧸ N) →₀ k[N]) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans
    ((Finsupp.domLCongr (normalQuotientCoordinatesEquiv N)).trans
      ((Finsupp.curryLinearEquiv k).trans
        (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))

@[simp] theorem restrictedRegularLinearEquiv_single (g : G) (r : k) :
    restrictedRegularLinearEquiv k N (MonoidAlgebra.single g r) =
      Finsupp.single (QuotientGroup.mk' N g)
        (MonoidAlgebra.single (normalQuotientPart N g) r) := by
  simp [restrictedRegularLinearEquiv, Finsupp.curryLinearEquiv,
    normalQuotientCoordinatesEquiv]

def restrictedRegularEquiv :
    (Rep.res N.subtype (Rep.leftRegular k G)).ρ.Equiv
      (Rep.finsupp (G ⧸ N) (Rep.leftRegular k N)).ρ :=
  Representation.Equiv.mk (restrictedRegularLinearEquiv k N) fun n => by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    change restrictedRegularLinearEquiv k N
        (Representation.leftRegular k G (n : G) (MonoidAlgebra.single g 1)) =
      ((Representation.leftRegular k N).finsupp (G ⧸ N)) n
        (restrictedRegularLinearEquiv k N (MonoidAlgebra.single g 1))
    have hq : QuotientGroup.mk' N ((n : G) * g) = QuotientGroup.mk' N g := by
      rw [map_mul, normalQuotient_mk_subgroup, one_mul]
    simp only [Representation.ofMulAction_single, smul_eq_mul,
      restrictedRegularLinearEquiv_single, Representation.finsupp_single,
      hq, normalQuotientPart_mul]

def restrictedRegularIso :
    Rep.res N.subtype (Rep.leftRegular k G) ≅
      Rep.finsupp (G ⧸ N) (Rep.leftRegular k N) :=
  Rep.mkIso (restrictedRegularEquiv k N)

end PolycyclicRecognition

end

end OAI
