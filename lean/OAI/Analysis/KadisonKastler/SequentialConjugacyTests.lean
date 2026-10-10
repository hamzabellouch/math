import OAI.Analysis.KadisonKastler.MeasurableStrongTests

namespace OAI

/-! # Sequential tests for the measurable conjugacy relation

Each represented algebra on a separable Hilbert space has an actual
sequence of contractions whose range is strongly dense in its unit ball.
Conjugacy is exactly two countable families of finite-vector tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure StrongUnitBallTestSequence (M : VonNeumannAlgebra H) where
  op : ℕ → H →L[ℂ] H
  mem : ∀ n, op n ∈ unitBall M
  dense : ∀ x ∈ unitBall M, ∃ T : ℕ → H →L[ℂ] H,
    (∀ n, T n ∈ Set.range op) ∧ ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (x ξ))

theorem exists_strongUnitBallTestSequence [SeparableSpace H] (M : VonNeumannAlgebra H) :
    Nonempty (StrongUnitBallTestSequence M) := by
  obtain ⟨E, hEc, hEM, hE⟩ := exists_countable_strong_dense_contractions
    (unitBall M) (fun _ hx => hx.2)
  obtain ⟨T, hTE, _⟩ := hE 0 (zero_mem_unitBall M)
  obtain ⟨a, ha⟩ := hEc.exists_eq_range ⟨T 0, hTE 0⟩
  refine ⟨⟨a, fun n => hEM (ha.symm ▸ Set.mem_range_self n), ?_⟩⟩
  intro x hx
  obtain ⟨S, hSE, hlim⟩ := hE x hx
  exact ⟨S, fun n => ha ▸ hSE n, hlim⟩

theorem StrongUnitBallTestSequence.range_subset {M : VonNeumannAlgebra H}
    (A : StrongUnitBallTestSequence M) : Set.range A.op ⊆ unitBall M := by
  rintro _ ⟨n, rfl⟩
  exact A.mem n

theorem conjugates_iff_strong_sequence_mem {M N : VonNeumannAlgebra H}
    (A : StrongUnitBallTestSequence M) (B : StrongUnitBallTestSequence N)
    (v : unitary (H →L[ℂ] H)) :
    Conjugates v M N ↔ (∀ j, unitaryConj v (A.op j) ∈ N) ∧
      (∀ j, unitaryConj (star v) (B.op j) ∈ M) := by
  constructor
  · intro hv
    exact ⟨fun j => hv.subset ⟨A.op j, (A.mem j).1, rfl⟩,
      fun j => hv.symm.subset ⟨B.op j, (B.mem j).1, rfl⟩⟩
  · rintro ⟨hA, hB⟩
    have hMN := unitaryConj_inclusion_of_dense_tests M N v (Set.range A.op) A.dense
      (by rintro _ ⟨j, rfl⟩; exact hA j)
    have hNM := unitaryConj_inclusion_of_dense_tests N M (star v) (Set.range B.op) B.dense
      (by rintro _ ⟨j, rfl⟩; exact hB j)
    apply Set.Subset.antisymm
    · exact hMN
    · intro y hy
      refine ⟨unitaryConj (star v) y, hNM ⟨y, hy, rfl⟩, ?_⟩
      simpa only [star_star] using unitaryConj_star_unitaryConj (star v) y

/-- This is the exact countable relation used for choosing implementers. -/
theorem conjugates_iff_countable_strong_tests {M N : VonNeumannAlgebra H}
    (A : StrongUnitBallTestSequence M) (B : StrongUnitBallTestSequence N)
    (ξ : ℕ → H) (hξ : DenseRange ξ) (v : unitary (H →L[ℂ] H)) :
    Conjugates v M N ↔
      (∀ j, CountableStrongTests ξ (Set.range B.op) (unitaryConj v (A.op j))) ∧
      (∀ j, CountableStrongTests ξ (Set.range A.op) (unitaryConj (star v) (B.op j))) := by
  rw [conjugates_iff_strong_sequence_mem A B v]
  apply and_congr
  · apply forall_congr'
    intro j
    exact mem_iff_countableStrongTests N ξ hξ (Set.range B.op) B.range_subset B.dense
      _ (by simpa only [norm_unitaryConj] using (A.mem j).2)
  · apply forall_congr'
    intro j
    exact mem_iff_countableStrongTests M ξ hξ (Set.range A.op) A.range_subset A.dense
      _ (by simpa only [norm_unitaryConj] using (B.mem j).2)

end

end KadisonKastler

end OAI
