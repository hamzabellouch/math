import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularEvaluationKernel
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TopHomologyKernel
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CohomologicalFiniteness
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

namespace OAI

/-! # Top homology represented by the regular-dual cokernel

For a bounded finite projective resolution, only the final differential is
needed. Its regular-dual cokernel represents homology in the top degree.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def boundedResolutionTopHomologyEquiv
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hfin : ∀ i, IntegralRepresentationFinite G (P.complex.X i))
    (hbound : IsZero (P.complex.X (n + 1))) (A : Rep ℤ G) :
    groupHomology A n ≃ₗ[ℤ]
      (cokernel (regularDualMap (P.complex.d n (n - 1))) ⟶ A) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  have hz : (P.complex.coinvariantsTensorObj A).d (n + 1) n = 0 := by
    change F.map (P.complex.d (n + 1) n) = 0
    rw [hbound.eq_of_src (P.complex.d (n + 1) n) 0, F.map_zero]
  let e := (groupHomologyIso A n P).toLinearEquiv.toAddEquiv.trans
    ((topHomologyKernelEquiv (P.complex.coinvariantsTensorObj A) n hz).toAddEquiv.trans
      (regularKernelCokernelEquiv (P.complex.d n (n - 1)) A
        (hfin n) (hfin (n - 1))).toAddEquiv)
  exact { e with map_smul' := fun r x => map_intCast_smul e ℤ ℤ r x }

end PolycyclicRecognition

end

end OAI
