import OAI.GroupTheory.PolycyclicRecognition.Finiteness.GroupIsoFiniteness
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

namespace OAI

/-! # Transport of regular-module cohomology and duality through group isomorphisms -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G J : Type} [Group G] [Group J]

def regularCohomologyGroupIso (e : G ≃* J) (i : ℕ) :
    groupCohomology (Rep.leftRegular k G) i ≅ groupCohomology (Rep.leftRegular k J) i :=
  groupCohomology.mapIso e (MonoidAlgebra.domCongr k k e).toLinearEquiv (by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro h
    apply LinearMap.ext_ring
    simp [map_mul]) i

theorem IsIntegralPoincareDualityGroup.of_equiv {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (e : G ≃* J) :
    IsIntegralPoincareDualityGroup J n := by
  refine ⟨hG.1.of_equiv e, ?_, ?_⟩
  · intro i hi
    exact IsZero.of_iso (hG.2.1 i hi) (regularCohomologyGroupIso ℤ e i).symm
  · obtain ⟨u⟩ := hG.2.2
    exact ⟨(regularCohomologyGroupIso ℤ e n).symm ≪≫ u⟩

end PolycyclicRecognition

end

end OAI
