import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredCone
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ))

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped Matrix.Norms.Operator

/-- The precise published linear realization supplies the faithful root
representation required by the measured cone construction. The choice of
height and every metric estimate remain separate from this input. -/
theorem nonempty_measuredCone_of_published_realization
    [SimplyConnectedSpace G] {a : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (existQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (integrateQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := F.N.modelSpace) (N := F.N.carrier)
        (EG := Q.modelSpace) (G := Q.carrier))
    (existI : NilpotentLieExistenceInput (M.coneWordIdeal C))
    (haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (integrateI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
        (EG := F.N.modelSpace) (G := F.N.carrier))
    : Nonempty (M.MeasuredCone F C) := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  have hr (v : cartanRootIdeal H) :
      (ρ.comp F.inclusionN) (F.ExpN (F.N.equiv v)) =
        algebraExpUnit ((j.comp (cartanRootIdeal H).incl) v) := by
    change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = algebraExpUnit (j v)
    rw [F.compatibleN, hmatch]
  exact M.nonempty_measuredCone (A := Matrix (Fin m) (Fin m) ℝ) F C
    haarN existQ haarQ integrateQ existI haarI integrateI
    (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) hr

end PolycyclicRecognition.CartanWordModel

end

end OAI
