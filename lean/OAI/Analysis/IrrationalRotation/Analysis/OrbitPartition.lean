import Mathlib
import OAI.Analysis.IrrationalRotation.Sampling.PrescribedPhaseRealization

namespace OAI

namespace Invariant233

open Set Function

theorem exists_finite_partition_of_nat_open_cover
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (U : ℕ → Set X) (hUopen : ∀ n, IsOpen (U n))
    (hcover : ∀ x, ∃ n, x ∈ U n) :
    ∃ H : ℕ, ∃ φ : ℕ → C(X, ℝ),
      (∀ n x, 0 ≤ φ n x) ∧
      (∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) ∧
      (∀ n, tsupport (φ n) ⊆ U n) ∧
      (∀ n, H < n → φ n = 0) := by
  classical
  obtain ⟨φ, hφsub⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUopen
    (by intro x _; simpa only [mem_iUnion] using hcover x)
  have hfinite : {n | (support (φ n)).Nonempty}.Finite :=
    φ.locallyFinite.finite_nonempty_of_compact
  let S := hfinite.toFinset
  let H := S.sup id
  have hindex : ∀ n x, φ n x ≠ 0 → n ≤ H := by
    intro n x hx
    apply Finset.le_sup (f := id)
    exact hfinite.mem_toFinset.mpr ⟨x, hx⟩
  refine ⟨H, fun n => φ n, φ.nonneg, ?_, hφsub, ?_⟩
  · intro x
    rw [← finsum_eq_sum_of_support_subset (fun n => φ n x)]
    · exact φ.sum_eq_one (mem_univ x)
    · intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hindex n x hn))
  · intro n hn
    ext x
    by_contra hx
    exact (not_le_of_gt hn) (hindex n x hx)

theorem exists_finite_orbit_partition
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (σ : X → X) (hσ : Continuous σ)
    (hdense : ∀ x, DenseRange (fun n : ℕ => σ^[n] x))
    (O : Set X) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ H : ℕ, ∃ φ : ℕ → C(X, ℝ),
      (∀ n x, 0 ≤ φ n x) ∧
      (∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) ∧
      (∀ n, σ^[n] '' tsupport (φ n) ⊆ O) ∧
      (∀ n, H < n → φ n = 0) := by
  obtain ⟨H, φ, hφpos, hφsum, hφsupport, hφzero⟩ :=
    exists_finite_partition_of_nat_open_cover (fun n => σ^[n] ⁻¹' O)
      (fun n => hO.preimage (hσ.iterate n))
      (fun x => (hdense x).exists_mem_open hO hOne)
  refine ⟨H, φ, hφpos, hφsum, ?_, hφzero⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hφsupport n hx

theorem exists_irrational_rotation_partition {θ : ℝ} (hθ : Irrational θ)
    (O : Set (AddCircle (1 : ℝ))) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ H : ℕ, ∃ φ : ℕ → C(AddCircle (1 : ℝ), ℝ),
      (∀ n x, 0 ≤ φ n x) ∧
      (∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) ∧
      (∀ n, (fun x => x + n • (θ : AddCircle (1 : ℝ))) '' tsupport (φ n) ⊆ O) ∧
      (∀ n, H < n → φ n = 0) := by
  have hn : DenseRange (fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) := by
    simpa only [Nat.add_zero] using
      PrescribedPhaseRealization.dense_positive_orbit_tail hθ 0
  have horbit : ∀ x : AddCircle (1 : ℝ),
      DenseRange (fun n : ℕ => (fun y => y + (θ : AddCircle (1 : ℝ)))^[n] x) := by
    intro x
    have hd := (Homeomorph.addLeft x).surjective.denseRange.comp hn
      (Homeomorph.addLeft x).continuous
    change DenseRange (fun n : ℕ => x + n • (θ : AddCircle (1 : ℝ))) at hd
    simpa only [add_right_iterate] using hd
  obtain ⟨H, φ, hφpos, hφsum, hφsupport, hφzero⟩ :=
    exists_finite_orbit_partition (fun x : AddCircle (1 : ℝ) => x + θ)
      (continuous_id.add continuous_const) horbit O hO hOne
  refine ⟨H, φ, hφpos, hφsum, ?_, hφzero⟩
  simpa only [add_right_iterate] using hφsupport

theorem exists_preparatory_partitions {θ : ℝ} (hθ : Irrational θ) :
    ∃ height : ℕ → ℕ, ∃ φ : ℕ → ℕ → C(AddCircle (1 : ℝ), ℝ),
      (∀ j n x, 0 ≤ φ j n x) ∧
      (∀ j x, ∑ n ∈ Finset.range (height j + 1), φ j n x = 1) ∧
      (∀ j, 1 ≤ j → ∀ n, ∀ x ∈ tsupport (φ j n),
        dist (x + (((n : ℝ) * θ : ℝ) : AddCircle (1 : ℝ))) 0 <
          1 / (10 * (j : ℝ))) ∧
      (∀ j n, height j < n → φ j n = 0) := by
  have hr : ∀ j : ℕ, 0 < (1 : ℝ) / (10 * ((j + 1 : ℕ) : ℝ)) := by
    intro j
    positivity
  choose H φ hnon hsum hsupport hzero using fun j : ℕ =>
    exists_irrational_rotation_partition hθ
      (Metric.ball 0 (1 / (10 * ((j + 1 : ℕ) : ℝ))))
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self (hr j)⟩
  refine ⟨fun j => H (j - 1), fun j => φ (j - 1),
    (fun j => hnon (j - 1)), (fun j => hsum (j - 1)), ?_,
    (fun j => hzero (j - 1))⟩
  intro j hj n x hx
  have h := hsupport (j - 1) n ⟨x, hx, rfl⟩
  change dist (x + n • (θ : AddCircle (1 : ℝ))) 0 <
    1 / (10 * ((j - 1 + 1 : ℕ) : ℝ)) at h
  simpa only [Nat.sub_add_cancel hj, ← AddCircle.coe_nsmul, nsmul_eq_mul] using h

end Invariant233

end OAI
