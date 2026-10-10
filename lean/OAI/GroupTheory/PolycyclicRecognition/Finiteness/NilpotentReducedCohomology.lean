import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CentralQuotientVanishing
import Mathlib.GroupTheory.Nilpotent

namespace OAI

/-! # Vanishing of reduced first cohomology for nilpotent groups

Induct on the nilpotency class through the quotient by the center, using the
orthogonal central decomposition and the explicit central averaging step.
-/

noncomputable section

namespace PolycyclicRecognition

universe u v

theorem unitaryReducedVanishing_nilpotent
    (G : Type u) [Group G] [Group.IsNilpotent G] :
    ∀ [TopologicalSpace G] [IsTopologicalGroup G], UnitaryReducedVanishing.{u, v} G := by
  apply Group.nilpotent_center_quotient_ind
    (P := fun H _ _ => ∀ [TopologicalSpace H] [IsTopologicalGroup H],
      UnitaryReducedVanishing.{u, v} H) G
  · intro H _ _ _ _
    exact unitaryReducedVanishing_of_subsingleton
  · intro H _ _ ih _ _
    exact unitaryReducedVanishing_of_centerQuotient ih

theorem reducedCohomologyInput_of_nilpotent
    {G : Type u} [Group G] [Group.IsNilpotent G] [TopologicalSpace G] [IsTopologicalGroup G]
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E] :
    ReducedCohomologyInput G E :=
  (unitaryReducedVanishing_nilpotent G).to_reduced E

end PolycyclicRecognition

end

end OAI
