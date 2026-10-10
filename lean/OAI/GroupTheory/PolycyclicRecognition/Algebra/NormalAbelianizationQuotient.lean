import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalAbelianizationModule
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationFiniteDescent

namespace OAI

/-! # The finite module over the actual quotient group ring -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem normalAbelianizationAut_trivial (n : N) :
    normalAbelianizationAut N (n : G) = 1 := by
  ext x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x
  change Abelianization.of (MulAut.conjNormal (H := N) (n : G) m) = Abelianization.of m
  have he : MulAut.conjNormal (H := N) (n : G) m = n * m * n⁻¹ := Subtype.ext rfl
  rw [he, map_mul, map_mul, map_inv]
  simp

def normalQuotientAbelianizationRepresentation :
    Representation ℤ (G ⧸ N) (Additive (Abelianization N)) :=
  QuotientGroup.lift N (normalAbelianizationRepresentation N) (by
    intro g hg
    apply LinearMap.ext
    intro x
    change Additive.ofMul (normalAbelianizationAut N g x.toMul) = x
    rw [normalAbelianizationAut_trivial N ⟨g, hg⟩]
    rfl)

theorem normalQuotientAbelianizationRepresentation_comp :
    (normalQuotientAbelianizationRepresentation N).comp (QuotientGroup.mk' N) =
      normalAbelianizationRepresentation N := by
  ext g x
  rfl

theorem finite_normalQuotientAbelianizationModule_of_normalGeneration
    (hN : N.IsFinitelyNormallyGenerated) :
    Module.Finite ℤ[G ⧸ N] (normalQuotientAbelianizationRepresentation N).asModule := by
  have hfg := finite_normalAbelianizationModule_of_normalGeneration N hN
  rw [← normalQuotientAbelianizationRepresentation_comp N] at hfg
  let := hfg
  exact finite_representation_of_comp (normalQuotientAbelianizationRepresentation N)
    (QuotientGroup.mk' N)

theorem finite_normalQuotientAbelianizationModule_of_abelian_quotient
    [Group.FG G] [IsMulCommutative (G ⧸ N)] :
    Module.Finite ℤ[G ⧸ N] (normalQuotientAbelianizationRepresentation N).asModule :=
  finite_normalQuotientAbelianizationModule_of_normalGeneration N
    (finitelyNormallyGenerated_of_abelian_quotient N)

end PolycyclicRecognition

end

end OAI
