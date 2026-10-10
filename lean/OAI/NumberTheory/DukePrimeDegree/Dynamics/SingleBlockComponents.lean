import OAI.NumberTheory.DukePrimeDegree.Dynamics.CanonicalSubgroupComponents
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockProjection
import OAI.NumberTheory.DukePrimeDegree.Dynamics.FiniteDiagonalVelocity

namespace OAI

/-!
# One actual root block and its canonical ergodic components

Ergodicity, diagonal velocity recurrence and the local block-preserving
stabilizer conclusion now refer to the same full-subgroup conditional
kernel. The selected root flow is ergodic on each component by Mautner;
no ergodicity of a selected diagonal element is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_singleBlock_component_ergodic_and_locally_block_preserving
    (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (k l : Fin (d + 1)) (hkl : k ≠ l) (hrkl : r k l) :
    let S : Set (Fin (d + 1)) := {i | r i k}
    let H := singleBlockRootGroup S
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X (d + 1))),
      let ν := condExpKernel μ (actionInvariantSigma H (X (d + 1))) z
      ErgodicSMul H (X (d + 1)) ν ∧
        (letI := rootTranslationAction hkl
         ErgodicSMul (Multiplicative ℝ) (X (d + 1)) ν) ∧
        {g : invariantRightSubgroup ν |
          slMatrixConjugation g.val (blockProjection (singleBlockSetoid S) k) =
            blockProjection (singleBlockSetoid S) k} ∈ 𝓝 (1 : invariantRightSubgroup ν) := by
  let S : Set (Fin (d + 1)) := {i | r i k}
  let H := singleBlockRootGroup S
  have hk : k ∈ S := r.refl k
  have hl : l ∈ S := r.symm hrkl
  have hH : H ≤ invariantRightSubgroup μ := by
    apply singleBlockRootGroup_le_of_roots
    intro i hi j hj hij t
    exact ((rootInvarianceRelation_iff_full_root hij μ).mp
      ((hr i j).mp (r.trans hi (r.symm hj)))) t
  have hAH : ∀ u : LogCoordinates d,
      diagonalFlow u ∈ Subgroup.normalizer (H : Set (G (d + 1))) := by
    intro u
    let ell : Fin (d + 1) → ℝ := Fin.snoc u (-∑ a, u a)
    have hell : ∑ a, ell a = 0 := by simp [ell, Fin.sum_univ_castSucc]
    have ha : diagonalOneParameter ell hell 1 = diagonalFlow u := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      congr 1
      funext a
      simp [ell]
    rw [← ha]
    exact diagonal_normalizes_singleBlockRootGroup S ell hell 1
  have hcomp := (lattice_canonical_subgroup_ergodic_decomposition H μ hH).2
  have hvel := ae_normalized_component_velocity_support d H hAH μ
  filter_upwards [hcomp, hvel] with z hz hVz
  let ν := condExpKernel μ (actionInvariantSigma H (X (d + 1))) z
  let : ErgodicSMul H (X (d + 1)) ν := hz
  have hHν : H ≤ invariantRightSubgroup ν :=
    subgroup_le_invariantRightSubgroup_of_invariant_action H ν
  refine ⟨hz, root_ergodic_of_single_block_ergodic S hkl hk hl ν, ?_⟩
  apply singleBlockProjection_fixed_near_identity (invariantRightSubgroup ν) S k l hkl hk hl
  · intro i hi j hj hij t
    exact hHν (root_mem_singleBlockRootGroup S i hi j hj hij t)
  · intro V hV i j hcross
    apply hVz V hV i j
    intro hij
    have hrij := (hr i j).mpr hij
    apply hcross
    change r i k ↔ r j k
    exact ⟨fun hi => r.trans (r.symm hrij) hi, fun hj => r.trans hrij hj⟩

end DukePrimeDegree

end

end OAI
