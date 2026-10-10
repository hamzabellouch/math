import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace OAI

/-!
# Finite patch nets and volume bounds for their active multiplicity

The net is chosen by maximal cardinality inside a totally bounded domain.
The active cardinality estimate is proved by disjoint half-radius balls;
the distance of active centers from the testing point is kept explicit.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

/-- Total boundedness makes every positive-radius packing number finite. -/
theorem packingNumber_ne_top_of_totallyBounded {A : Set X} (hA : TotallyBounded A)
    {r : ℝ≥0} (hr : r ≠ 0) : Metric.packingNumber r A ≠ ⊤ := by
  obtain ⟨C, _, hC, hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded
    (show r / 2 ≠ 0 by positivity) hA
  have hp : Metric.packingNumber r A ≤ C.encard := by
    calc
      _ = Metric.packingNumber (2 * (r / 2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (r / 2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ _ := hcover.externalCoveringNumber_le_encard
  exact ne_top_of_le_ne_top hC.encard_lt_top.ne hp

/-- The standard maximal separated set is finite even in the fallback case. -/
theorem finite_maximalSeparatedSet (r : ℝ≥0) (A : Set X) :
    (Metric.maximalSeparatedSet r A).Finite := by
  by_cases h : Metric.packingNumber r A = ⊤
  · simp [Metric.maximalSeparatedSet, h]
  · apply Set.encard_ne_top_iff.mp
    rwa [Metric.encard_maximalSeparatedSet h]

/-- A concrete finite maximal-cardinality net. -/
def maximalPatchNet (r : ℝ≥0) (A : Set X) : Finset X :=
  (finite_maximalSeparatedSet r A).toFinset

@[simp] theorem coe_maximalPatchNet (r : ℝ≥0) (A : Set X) :
    (maximalPatchNet r A : Set X) = Metric.maximalSeparatedSet r A := by
  simp [maximalPatchNet]

theorem maximalPatchNet_subset (r : ℝ≥0) (A : Set X) :
    (maximalPatchNet r A : Set X) ⊆ A := by
  rw [coe_maximalPatchNet]
  exact Metric.maximalSeparatedSet_subset

theorem maximalPatchNet_separated (r : ℝ≥0) (A : Set X) :
    (maximalPatchNet r A : Set X).Pairwise (fun x y => (r : ℝ) < dist x y) := by
  intro x hx y hy hxy
  have hsep := Metric.isSeparated_maximalSeparatedSet (ε := r) (A := A)
  rw [← coe_maximalPatchNet] at hsep
  have hh := hsep hx hy hxy
  have hd : r < nndist x y := by
    simpa only [edist_nndist, ENNReal.coe_lt_coe] using hh
  exact_mod_cast hd

theorem maximalPatchNet_covers {r : ℝ≥0} {A : Set X}
    (hr : r ≠ 0) (hA : TotallyBounded A) :
    ∀ x ∈ A, ∃ y ∈ maximalPatchNet r A, dist x y ≤ r := by
  intro x hx
  have hc := Metric.isCover_maximalSeparatedSet
    (packingNumber_ne_top_of_totallyBounded hA hr)
  obtain ⟨y, hy, hd⟩ := hc hx
  change edist x y ≤ (r : ℝ≥0∞) at hd
  refine ⟨y, ?_, ?_⟩
  · simpa only [← coe_maximalPatchNet, Finset.mem_coe] using hy
  · have hd' : nndist x y ≤ r := by
      simpa only [edist_nndist, ENNReal.coe_le_coe] using hd
    exact_mod_cast hd'

/-- Maximality is by cardinality, and therefore also rules out adding any
new separated point from the original domain. -/
theorem maximalPatchNet_card_maximal {r : ℝ≥0} {A : Set X}
    (hr : r ≠ 0) (hA : TotallyBounded A) (s : Finset X)
    (hsub : (s : Set X) ⊆ A) (hsep : Metric.IsSeparated r (s : Set X)) :
    s.card ≤ (maximalPatchNet r A).card := by
  have hh := Metric.encard_le_of_isSeparated hsub hsep
    (packingNumber_ne_top_of_totallyBounded hA hr)
  rw [← coe_maximalPatchNet] at hh
  exact_mod_cast hh

/-- In a proper metric space every bounded domain admits the finite net,
even when the domain is not closed. -/
theorem maximalPatchNet_covers_bounded [ProperSpace X] {r : ℝ≥0} {A : Set X}
    (hr : r ≠ 0) (hA : Bornology.IsBounded A) :
    ∀ x ∈ A, ∃ y ∈ maximalPatchNet r A, dist x y ≤ r :=
  maximalPatchNet_covers hr (hA.isCompact_closure.totallyBounded.subset subset_closure)

/-- Half-radius balls around separated centers are pairwise disjoint. -/
theorem separated_half_balls_disjoint (s : Finset X) {r : ℝ}
    (hsep : (s : Set X).Pairwise (fun x y => r ≤ dist x y)) :
    Set.PairwiseDisjoint (s : Set X) (fun y => Metric.ball y (r / 2)) := by
  intro x hx y hy hxy
  apply Metric.ball_disjoint_ball
  have hh := hsep hx hy hxy
  linarith

section Volume

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The disjoint-ball packing estimate, with no volume comparison hidden in
the statement. Finite measure is only required for the containing ball. -/
theorem separated_card_mul_volume_le (μ : Measure X) (s : Finset X) (x : X)
    {r R v : ℝ}
    (hsep : (s : Set X).Pairwise (fun y z => r ≤ dist y z))
    (hnear : ∀ y ∈ s, dist y x ≤ R)
    (hlower : ∀ y ∈ s, v ≤ μ.real (Metric.ball y (r / 2)))
    (hfinite : μ (Metric.ball x (R + r / 2)) ≠ ∞) :
    (s.card : ℝ) * v ≤ μ.real (Metric.ball x (R + r / 2)) := by
  have hsub (y : X) (hy : y ∈ s) : Metric.ball y (r / 2) ⊆
      Metric.ball x (R + r / 2) := Metric.ball_subset_ball' (by linarith [hnear y hy])
  have hunion : (⋃ y ∈ s, Metric.ball y (r / 2)) ⊆ Metric.ball x (R + r / 2) := by
    intro z hz
    obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.mp hz
    exact hsub y hy hz
  calc
    _ = ∑ y ∈ s, v := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ s, μ.real (Metric.ball y (r / 2)) := Finset.sum_le_sum hlower
    _ = μ.real (⋃ y ∈ s, Metric.ball y (r / 2)) :=
      (measureReal_biUnion_finset (separated_half_balls_disjoint s hsep)
        (fun _ _ => isOpen_ball.measurableSet)
        (fun y hy => measure_ne_top_of_subset (hsub y hy) hfinite)).symm
    _ ≤ _ := measureReal_mono hunion hfinite

/-- Two-sided Euclidean volume bounds yield a radius-independent real
cardinality bound for centers within `C₀ * r` of the testing point. -/
theorem separated_card_le_of_euclidean_volume (μ : Measure X) (s : Finset X) (x : X)
    (n : ℕ) {r C₀ a b : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hsep : (s : Set X).Pairwise (fun y z => r ≤ dist y z))
    (hnear : ∀ y ∈ s, dist y x ≤ C₀ * r)
    (hlower : ∀ y ∈ s, a * (r / 2) ^ n ≤ μ.real (Metric.ball y (r / 2)))
    (hupper : μ.real (Metric.ball x (C₀ * r + r / 2)) ≤ b * (C₀ * r + r / 2) ^ n)
    (hfinite : μ (Metric.ball x (C₀ * r + r / 2)) ≠ ∞) :
    (s.card : ℝ) ≤ b / a * (2 * C₀ + 1) ^ n := by
  have hp := (separated_card_mul_volume_le μ s x hsep hnear hlower hfinite).trans hupper
  have hrad : C₀ * r + r / 2 = (2 * C₀ + 1) * (r / 2) := by ring
  rw [hrad, mul_pow] at hp
  have hpow : 0 < (r / 2) ^ n := pow_pos (by linarith) _
  have hc : (s.card : ℝ) * a ≤ b * (2 * C₀ + 1) ^ n := by
    apply (mul_le_mul_iff_left₀ hpow).mp
    convert hp using 1 <;> ring
  have hd := (le_div_iff₀ ha).mpr hc
  convert hd using 1
  ring

/-- An integer uniform multiplicity constant extracted from the volume
ratio. No cardinal bound is supplied as a premise. -/
theorem separated_card_le_ceil_of_euclidean_volume (μ : Measure X) (s : Finset X) (x : X)
    (n : ℕ) {r C₀ a b : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hsep : (s : Set X).Pairwise (fun y z => r ≤ dist y z))
    (hnear : ∀ y ∈ s, dist y x ≤ C₀ * r)
    (hlower : ∀ y ∈ s, a * (r / 2) ^ n ≤ μ.real (Metric.ball y (r / 2)))
    (hupper : μ.real (Metric.ball x (C₀ * r + r / 2)) ≤ b * (C₀ * r + r / 2) ^ n)
    (hfinite : μ (Metric.ball x (C₀ * r + r / 2)) ≠ ∞) :
    s.card ≤ ⌈b / a * (2 * C₀ + 1) ^ n⌉₊ := by
  have hh := separated_card_le_of_euclidean_volume μ s x n hr ha hsep hnear hlower hupper hfinite
  exact_mod_cast hh.trans (Nat.le_ceil _)

/-- The active subfamily of a net satisfies the same uniform cardinal
bound whenever active centers lie within `C₀ * r` of the point. -/
theorem active_maximalPatchNet_card_le (μ : Measure X) (A : Set X)
    (r : ℝ≥0) (x : X) (active : X → Prop) [DecidablePred active] (n : ℕ)
    (hr : 0 < r) {C₀ a b : ℝ} (ha : 0 < a)
    (hnear : ∀ y ∈ maximalPatchNet r A, active y → dist y x ≤ C₀ * r)
    (hlower : ∀ y ∈ maximalPatchNet r A, active y →
      a * ((r : ℝ) / 2) ^ n ≤ μ.real (Metric.ball y (r / 2)))
    (hupper : μ.real (Metric.ball x (C₀ * r + r / 2)) ≤ b * (C₀ * r + r / 2) ^ n)
    (hfinite : μ (Metric.ball x (C₀ * r + r / 2)) ≠ ∞) :
    ((maximalPatchNet r A).filter active).card ≤ ⌈b / a * (2 * C₀ + 1) ^ n⌉₊ := by
  apply separated_card_le_ceil_of_euclidean_volume μ _ x n (by exact_mod_cast hr) ha
  · intro y hy z hz hne
    exact (maximalPatchNet_separated r A (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hz).1 hne).le
  · intro y hy
    exact hnear y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  · intro y hy
    exact hlower y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  · exact hupper
  · exact hfinite

end Volume

end RegularPointCoordinates

end

end OAI
