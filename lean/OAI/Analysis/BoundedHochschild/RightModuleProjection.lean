import OAI.Analysis.BoundedHochschild.SimultaneousModuleAverages
import OAI.Analysis.BoundedHochschild.JointAveragingRelations
import OAI.Analysis.BoundedHochschild.CompletelyBoundedMapSpace

namespace OAI

/-! The right-module averaging projection, with its linearity, norm bound,
and covariance under input and output left multiplication. This is the
specialization of Sinclair–Smith (1998), Theorem 3.4, used in cohomology. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma norm_le_of_weakRightAverageOrbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T S : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C)
    (hS : weakOperatorImage e S ∈ weakRightAverageOrbit e T) : ‖S‖ ≤ C := by
  obtain ⟨U, hU, hUS⟩ := weakOperatorBall_realize e hT.1
    (weakRightAverageOrbit_subset_ball e hno T hT hS)
  exact (weakOperatorImage_injective e hUS) ▸ hU

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma module_map_weakRightAverageOrbit_singleton (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) (hT : ∀ a b, T (a*b) = T a * b) :
    weakRightAverageOrbit e T ⊆ {weakOperatorImage e T} := by
  have hfix := (fixed_right_averages_iff T).mpr (right_module_eq_left_multiplication T hT)
  apply closure_minimal _ isClosed_singleton
  rintro F ⟨S, ⟨n, m, hm, rfl⟩, rfl⟩
  rw [hfix n m hm]
  rfl

structure RightModuleAveragingProjection where
  map : CompletelyBoundedMap M →ₗ[ℂ] (M →L[ℂ] M)
  bound : ∀ T C, CompletelyBoundedEstimate T.val C → ‖map T‖ ≤ C
  module : ∀ T a b, map T (a*b) = map T a * b
  covariance : ∀ a b T, map (cbLeftSandwich a b T) = leftSandwichMap a b (map T)
  fixes : ∀ T, (∀ a b, T.val (a*b) = T.val a * b) → map T = T.val

theorem exists_rightModuleAveragingProjection [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M) :
    Nonempty (RightModuleAveragingProjection (M := M)) := by
  obtain ⟨S, hS, hSorb⟩ := exists_simultaneous_right_module_average e hno
    (fun T : CompletelyBoundedMap M => T.val) completelyBoundedBound completelyBoundedBound_spec
  let P : CompletelyBoundedMap M →ₗ[ℂ] (M →L[ℂ] M) :=
    { toFun := S
      map_add' := by
        intro T U
        apply weakOperatorImage_injective e
        rw [weakOperatorImage_add]
        exact joint_orbit_add_relation e (fun T : CompletelyBoundedMap M => T.val) rfl hSorb
      map_smul' := by
        intro z T
        apply weakOperatorImage_injective e
        rw [weakOperatorImage_complex_smul]
        exact joint_orbit_smul_relation e (fun T : CompletelyBoundedMap M => T.val) z rfl hSorb }
  refine ⟨{ map := P, bound := ?_, module := ?_, covariance := ?_, fixes := ?_ }⟩
  · intro T C hTC
    exact norm_le_of_weakRightAverageOrbit e hno T.val (S T) hTC
      (weakFamilyAverageOrbit_component e (fun T : CompletelyBoundedMap M => T.val) T hSorb)
  · exact fun T => (hS T).2
  · intro a b T
    apply weakOperatorImage_injective e
    rw [← weakLeftSandwich_image]
    exact joint_orbit_sandwich_relation e (fun T : CompletelyBoundedMap M => T.val) a b rfl hSorb
  · intro T hT
    apply weakOperatorImage_injective e
    exact module_map_weakRightAverageOrbit_singleton e T.val hT
      (weakFamilyAverageOrbit_component e (fun T : CompletelyBoundedMap M => T.val) T hSorb)

end BoundedHochschild.KadisonRingrose

end

end OAI
