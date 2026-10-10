import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BoundedResolutionTopHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RegularDualCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DimensionFromRegularCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteResolutionTruncation

namespace OAI

/-! # Top homology of an integral Poincare duality group

The orientation representation is the regular-dual cokernel of the last
resolution differential. Its underlying integral module is rank one, and
maps from it represent top-degree homology with arbitrary coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem IsIntegralPoincareDualityGroup.topHomology_orientation {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ D : Rep ℤ G, Nonempty (D.V ≃ₗ[ℤ] ℤ) ∧
      ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)) := by
  classical
  obtain ⟨P, _, hfin, _⟩ := hG.1
  let := hG.cohomologicalDimension
  let Q := finiteProjectiveResolution P n
  have hQfin : ∀ i, IntegralRepresentationFinite G (Q.complex.X i) :=
    finiteTruncation_finite P n (fun i _ => hfin i)
  have hQbound : IsZero (Q.complex.X (n + 1)) :=
    finiteTruncation_isZero P n (n + 1) (by omega)
  let D := cokernel (regularDualMap (Q.complex.d n (n - 1)))
  obtain ⟨e⟩ := hG.2.2
  refine ⟨D, ⟨((regularDualCokernelCohomologyIso Q n hQbound).trans e).toLinearEquiv⟩, ?_⟩
  intro A
  exact ⟨boundedResolutionTopHomologyEquiv Q n hQfin hQbound A⟩

end PolycyclicRecognition

end

end OAI
