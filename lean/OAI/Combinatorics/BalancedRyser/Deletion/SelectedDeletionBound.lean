import OAI.Combinatorics.BalancedRyser.Deletion.DeletionDomination2
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionCoordinates

namespace OAI

open scoped BigOperators

namespace Balanced.SelectedDeletion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem atom_le_of_fixed_cylinders {κ : Kernel F} {K : ℝ}
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (M : MergedPairs F) (f : Output F) :
    κ M f ≤ (K / Fintype.card F) ^ (2 * (Fintype.card F + 1)) := by
  classical
  have h := hcyl M Finset.univ f
  have heq : ∀ g : Output F,
      (∀ i ∈ (Finset.univ : Finset (Slot F)), g i = f i) ↔ g = f := by
    intro g
    simp only [Finset.mem_univ, forall_const, funext_iff]
  unfold fixedCylinderMass at h
  simp_rw [heq] at h
  simpa [Slot, Direction, Nat.mul_comm] using h

theorem deletionJointMass_le_of_atom_bound (κ : Kernel F)
    (hnonneg : ∀ M f, 0 ≤ κ M f) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ M f, κ M f ≤ b) (D : DeletionSet F 3) :
    deletionJointMass κ D ≤ (6 : ℝ) ^ (Fintype.card F + 1) *
      (b / (Fintype.card F : ℝ) ^ (Fintype.card F + 1)) := by
  classical
  rw [SelectedDeletionCoordinates.deletionJointMass_eq_fiber_sum]
  let W := fun m₀ m₁ f => κ (SelectedDeletionCoordinates.offsetPairEquiv (m₀, m₁)) f
  have hw : ∀ ω : SelectedDeletionCoordinates.SingleOffsets F ×
      SelectedDeletionCoordinates.SplitOffsets F,
      0 ≤ UniformKernel.fiberMass W ω.1 ω.2 := by
    intro ω
    exact UniformKernel.fiberMass_nonneg W (fun m₀ m₁ f => hnonneg _ _) _ _
  have hcard : ∀ d, (DeletionCoordinates.fiber D.val d).card = 3 := by
    intro d
    rw [← DeletionCoordinates.card_filter_direction]
    exact D.property d
  have hc : 0 ≤ b / Fintype.card (SelectedDeletionCoordinates.SingleOffsets F) :=
    div_nonneg hb (Nat.cast_nonneg _)
  have h := DeletionAssignments.weighted_unordered_deletion_le_of_injective_roles
    (fun ω : SelectedDeletionCoordinates.SingleOffsets F × SelectedDeletionCoordinates.SplitOffsets F =>
      UniformKernel.fiberMass W ω.1 ω.2) hw
    SelectedDeletionCoordinates.roles SelectedDeletionCoordinates.roles_injective
    (DeletionCoordinates.fiber D.val) hcard
    (b / Fintype.card (SelectedDeletionCoordinates.SingleOffsets F)) hc
    (fun ω => UniformKernel.fiberMass_le W b (fun _ _ _ => hbound _ _) ω.1 ω.2)
  simpa only [SelectedDeletionCoordinates.SingleOffsets, Fintype.card_fun,
    Direction, Fintype.card_option, Nat.cast_pow] using h

theorem deletionJointMass_le_assignments {κ : Kernel F} {K : ℝ}
    (hK : 0 ≤ K) (hnonneg : ∀ M f, 0 ≤ κ M f)
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (D : DeletionSet F 3) :
    deletionJointMass κ D ≤
      (6 * K ^ 2 / (Fintype.card F : ℝ) ^ 3) ^ (Fintype.card F + 1) := by
  have h := deletionJointMass_le_of_atom_bound κ hnonneg
    ((K / Fintype.card F) ^ (2 * (Fintype.card F + 1)))
    (by positivity) (atom_le_of_fixed_cylinders hcyl) D
  exact h.trans_eq (DeletionLaw.assignment_factorization _ _ K)

theorem realizesConditionalLaw_dominated {κ : Kernel F} {K a₀ : ℝ}
    (hq : 3 ≤ Fintype.card F) (hK : 0 ≤ K) (ha₀ : 0 < a₀)
    (hnonneg : ∀ M f, 0 ≤ κ M f)
    (hcyl : ∀ M (J : Finset (Slot F)) (f : Output F),
      fixedCylinderMass κ M J f ≤ (K / Fintype.card F) ^ J.card)
    (hsuccess : a₀ ≤ successMass κ)
    (Q : PMF (DeletionSet F 3)) (hQ : RealizesConditionalLaw κ Q) :
    DeletionDominated 3 (a₀⁻¹ + 4 * K) Q := by
  intro D
  rw [hQ D]
  have hspos : 0 < successMass κ := ha₀.trans_le hsuccess
  have hraw := deletionJointMass_le_of_atom_bound κ hnonneg
    ((K / Fintype.card F) ^ (2 * (Fintype.card F + 1)))
    (by positivity) (atom_le_of_fixed_cylinders hcyl) D
  have hfinite := hraw.trans (DeletionLaw.assignment_bound_le_uniform hq K)
  have hu : 0 ≤ DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) := by
    unfold DeletionLaw.uniformDeletionMass
    positivity
  have hcoef : 0 ≤ K ^ (2 * (Fintype.card F + 1)) := by positivity
  calc
    deletionJointMass κ D / successMass κ ≤
        (K ^ (2 * (Fintype.card F + 1)) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1)) / a₀ :=
      (div_le_div_of_nonneg_right hfinite hspos.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg hcoef hu) ha₀ hsuccess)
    _ = (a₀⁻¹ * K ^ (2 * (Fintype.card F + 1))) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) := by ring
    _ ≤ Real.exp ((a₀⁻¹ + 4 * K) * (Fintype.card F : ℝ)) *
          DeletionLaw.uniformDeletionMass (Fintype.card F) (Fintype.card F + 1) :=
      mul_le_mul_of_nonneg_right
        (BalancedRyser.deletion_ratio_exponential_envelope ha₀ hK (by omega)) hu
    _ = Real.exp ((a₀⁻¹ + 4 * K) * (Fintype.card F : ℝ)) *
          uniformDeletionMass (F := F) 3 := by
      rw [GeometricDeletionCounting.uniformDeletionMass_eq]
      rfl

end Balanced.SelectedDeletion

end OAI
