import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePacking
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace OAI

/-! # Lower packing bounds from Haar volume

A totally bounded endpoint set has a finite separated net. Its volume is
at most the cardinality of that net times the mass of a fixed-radius ball.
This is the lower packing estimate used after stationary mesh selection.
-/

noncomputable section

open Metric Set MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

/-- A totally bounded set admits a finite separated net with its centers
inside the set. The set itself need not be closed or measurable. -/
theorem exists_separated_net_of_totallyBounded
    {X : Type*} [PseudoMetricSpace X] {S : Set X} (hS : TotallyBounded S)
    {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  obtain ⟨U, _hUS, hUfin, hUcover⟩ := finite_approx_of_totallyBounded hS (r / 3) (by positivity)
  let u := hUfin.toFinset
  have hbound (t : Finset X) (ht : (↑t : Set X) ⊆ S)
      (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) : t.card ≤ u.card := by
    have hchoice (x : {x // x ∈ t}) : ∃ y : {y // y ∈ u}, dist x.val y.val < r / 3 := by
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hUcover (ht x.property))
      exact ⟨⟨y, hUfin.mem_toFinset.mpr hy⟩, Metric.mem_ball.mp hxy⟩
    choose c hc using hchoice
    have hinj : Function.Injective c := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hdist : dist x.val y.val < r := by
        calc
          dist x.val y.val ≤ dist x.val (c x).val + dist (c x).val y.val := dist_triangle _ _ _
          _ = dist x.val (c x).val + dist y.val (c y).val := by rw [hxy, dist_comm (c y).val]
          _ < r := by linarith [hc x, hc y]
      exact (not_lt_of_ge hdist.le) (hsep x.val x.property y.val y.property hne)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective c hinj
  obtain ⟨t, ht, hsep, _hcard, hcover⟩ :=
    finite_separated_cover_set_of_bound S hr.le u.card hbound
  exact ⟨t, ht, hsep, hcover⟩

variable {G : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

omit [BorelSpace G] in
/-- Haar mass of a closed ball is independent of its center. -/
theorem measure_closedBall_eq_identity (μ : Measure G) [μ.IsMulLeftInvariant]
    (x : G) (r : ℝ) : μ (closedBall x r) = μ (closedBall (1 : G) r) := by
  have h := measure_preimage_mul μ x (closedBall x r)
  rw [preimage_mul_left_closedBall, inv_mul_cancel] at h
  exact h.symm

omit [BorelSpace G] in
/-- The volume of an arbitrary endpoint set bounds below the cardinality
of one finite separated subset. No measurability of the endpoint set is needed. -/
theorem exists_separated_net_volume_bound (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : TotallyBounded S) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (closedBall (1 : G) r) := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded hS hr
  refine ⟨t, ht, hsep, ?_⟩
  calc
    μ S ≤ μ (⋃ x ∈ t, closedBall x r) := measure_mono (by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hcover x hx
      exact Set.mem_iUnion₂.mpr ⟨y, hy, by simpa only [mem_closedBall, dist_comm] using hxy⟩)
    _ ≤ ∑ x ∈ t, μ (closedBall x r) := measure_biUnion_finset_le _ _
    _ = _ := by simp [measure_closedBall_eq_identity, nsmul_eq_mul]

end PolycyclicRecognition

end

end OAI
