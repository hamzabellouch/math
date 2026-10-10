import OAI.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L σ τ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_kernelProjection_external_net
    (T : X → D.Niltest w) (centers : Fin n → D.Niltest v)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {p ε : ℝ} (hT : ∀ x, (T x).UnitIntervalValued)
    (hTc : ∀ x, (T x).ComplexityLE p)
    (hcenters : ∀ i, (centers i).UnitIntervalValued)
    (hcentersc : ∀ i, (centers i).ComplexityLE p)
    (hnet : ∀ x, ∃ i, ∀ y, ‖(T x).observable y - (centers i).observable y‖ ≤ ε) :
    ∃ (S : X → D.Niltest w) (projectedCenters : Fin n → D.Niltest v),
      (∀ x, S x = (T x).kernelProjection K hK) ∧
      (∀ i, projectedCenters i = (centers i).kernelProjection K hK) ∧
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE p ∧
        (S x).orbit = (T x).orbit ∧ (S x).normBound = (T x).normBound ∧
        (S x).lipBound = (T x).lipBound) ∧
      (∀ i, (projectedCenters i).UnitIntervalValued ∧
        (projectedCenters i).ComplexityLE p ∧
        (projectedCenters i).orbit = (centers i).orbit ∧
        (projectedCenters i).normBound = (centers i).normBound ∧
        (projectedCenters i).lipBound = (centers i).lipBound) ∧
      (∀ x, ∃ i, ∀ y, ‖(S x).observable y - (projectedCenters i).observable y‖ ≤ ε) ∧
      ∀ i, (∃ x, (centers i).observable = (T x).observable) →
        ∃ x, (projectedCenters i).observable = (S x).observable := by
  let S := fun x => (T x).kernelProjection K hK
  let C := fun i => (centers i).kernelProjection K hK
  refine ⟨S, C, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(T x).kernelProjection_unitInterval K hK (hT x),
      (T x).kernelProjection_complexity K hK (hTc x), rfl, rfl, rfl⟩
  · intro i
    exact ⟨(centers i).kernelProjection_unitInterval K hK (hcenters i),
      (centers i).kernelProjection_complexity K hK (hcentersc i), rfl, rfl, rfl⟩
  · intro x
    obtain ⟨i, hi⟩ := hnet x
    exact ⟨i, (T x).kernelProjection_observable_sub_norm_le (centers i) K hK hi⟩
  · intro i hi
    obtain ⟨x, hx⟩ := hi
    refine ⟨x, funext fun y => sub_eq_zero.mp (norm_eq_zero.mp ?_)⟩
    apply le_antisymm _ (norm_nonneg _)
    apply (centers i).kernelProjection_observable_sub_norm_le (T x) K hK
    intro z
    rw [hx, sub_self, norm_zero]

theorem exists_kernelProjection_member_external_net
    (T : X → D.Niltest w) (representative : Fin n → X)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {p ε : ℝ} (hT : ∀ x, (T x).UnitIntervalValued)
    (hTc : ∀ x, (T x).ComplexityLE p)
    (hnet : ∀ x, ∃ i, ∀ y,
      ‖(T x).observable y - (T (representative i)).observable y‖ ≤ ε) :
    ∃ (S : X → D.Niltest w) (projectedCenters : Fin n → D.Niltest w),
      (∀ x, S x = (T x).kernelProjection K hK) ∧
      (∀ i, projectedCenters i = S (representative i)) ∧
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE p ∧
        (S x).orbit = (T x).orbit ∧ (S x).normBound = (T x).normBound ∧
        (S x).lipBound = (T x).lipBound) ∧
      (∀ x, ∃ i, ∀ y, ‖(S x).observable y - (projectedCenters i).observable y‖ ≤ ε) ∧
      ∀ i, ∃ x, projectedCenters i = S x := by
  let S := fun x => (T x).kernelProjection K hK
  refine ⟨S, fun i => S (representative i), fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(T x).kernelProjection_unitInterval K hK (hT x),
      (T x).kernelProjection_complexity K hK (hTc x), rfl, rfl, rfl⟩
  · intro x
    obtain ⟨i, hi⟩ := hnet x
    exact ⟨i, (T x).kernelProjection_observable_sub_norm_le
      (T (representative i)) K hK hi⟩
  · intro i
    exact ⟨representative i, rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
