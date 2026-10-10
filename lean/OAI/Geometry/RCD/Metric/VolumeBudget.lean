import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace OAI

/-!
# The dyadic volume-defect budget

Successive volume increments telescope, while the rescaled curvature
contribution is a geometric series.  Both monotone bounded profiles and raw
profiles converging to a bounded density are treated.  This is the scalar
summation argument in the proof of the manuscript's Poisson pinching lemma.
-/

open scoped BigOperators
open Filter
open scoped Topology

namespace RegularPointCoordinates

/-- The finite sum of consecutive normalized-volume increments telescopes. -/
theorem volume_profile_increment_sum (A : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range k, (A (i + 1) - A i)) = A k - A 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The curvature correction at dyadic radii has total mass at most `4 / 3`. -/
theorem sum_range_quarter_pow_le (k : ℕ) :
    (∑ i ∈ Finset.range k, (1 / 4 : ℝ) ^ i) ≤ 4 / 3 := by
  have hexact : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (1 / 4 : ℝ) ^ i) =
        (4 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ k) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [hexact]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) k]

/-- A monotone volume profile bounded by Euclidean volume has summable
successive increments. -/
theorem volume_profile_increments_summable {A : ℕ → ℝ} {omega : ℝ}
    (hmono : Monotone A) (hupper : ∀ i, A i ≤ omega) :
    Summable (fun i => A (i + 1) - A i) := by
  apply summable_of_sum_range_le
    (c := omega - A 0) (fun i => sub_nonneg.mpr (hmono (Nat.le_succ i)))
  intro k
  rw [volume_profile_increment_sum]
  exact sub_le_sub_right (hupper k) (A 0)

/-- Finite Poisson-defect sums are controlled by the corresponding volume
drop and the partial curvature series. -/
theorem volume_defect_partial_sum_telescope {A P : ℕ → ℝ} {C kappa : ℝ}
    (hbound : ∀ i, P i ≤ C * (A (i + 1) - A i + kappa * (1 / 4 : ℝ) ^ i))
    (k : ℕ) :
    (∑ i ∈ Finset.range k, P i) ≤
      C * (A k - A 0 + kappa * ∑ i ∈ Finset.range k, (1 / 4 : ℝ) ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith [hbound k]

/-- Uniform finite-scale bound by the initial volume deficit and curvature. -/
theorem volume_defect_partial_sum_le {A P : ℕ → ℝ} {C kappa omega : ℝ}
    (hC : 0 ≤ C) (hkappa : 0 ≤ kappa) (hupper : ∀ i, A i ≤ omega)
    (hbound : ∀ i, P i ≤ C * (A (i + 1) - A i + kappa * (1 / 4 : ℝ) ^ i))
    (k : ℕ) :
    (∑ i ∈ Finset.range k, P i) ≤ C * (omega - A 0 + kappa * (4 / 3)) := by
  refine (volume_defect_partial_sum_telescope hbound k).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add (sub_le_sub_right (hupper k) (A 0))
    (mul_le_mul_of_nonneg_left (sum_range_quarter_pow_le k) hkappa)

/-- Comparison with the summable volume increments and curvature series
proves summability of the nonnegative defects. -/
theorem volume_defect_summable {A P : ℕ → ℝ} {C kappa omega : ℝ}
    (hmono : Monotone A) (hupper : ∀ i, A i ≤ omega) (hP : ∀ i, 0 ≤ P i)
    (hbound : ∀ i, P i ≤ C * (A (i + 1) - A i + kappa * (1 / 4 : ℝ) ^ i)) :
    Summable P := by
  have hgeom : Summable (fun i : ℕ => (1 / 4 : ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmajor : Summable
      (fun i => C * (A (i + 1) - A i + kappa * (1 / 4 : ℝ) ^ i)) :=
    ((volume_profile_increments_summable hmono hupper).add
      (hgeom.mul_left kappa)).mul_left C
  exact Summable.of_nonneg_of_le hP hbound hmajor

/-- The complete defect budget depends only on the initial volume deficit
and the curvature parameter. -/
theorem volume_defect_tsum_le {A P : ℕ → ℝ} {C kappa omega : ℝ}
    (hC : 0 ≤ C) (hkappa : 0 ≤ kappa) (hupper : ∀ i, A i ≤ omega)
    (hP : ∀ i, 0 ≤ P i)
    (hbound : ∀ i, P i ≤ C * (A (i + 1) - A i + kappa * (1 / 4 : ℝ) ^ i)) :
    (∑' i, P i) ≤ C * (omega - A 0 + kappa * (4 / 3)) := by
  exact Real.tsum_le_of_sum_range_le hP
    (volume_defect_partial_sum_le hC hkappa hupper hbound)

/-- Summability and the quantitative total bound in one application. -/
theorem volume_defect_budget {A P : ℕ → ℝ} {C kappa omega : ℝ}
    (hC : 0 ≤ C) (hkappa : 0 ≤ kappa)
    (hmono : Monotone A) (hupper : ∀ i, A i ≤ omega) (hP : ∀ i, 0 ≤ P i)
    (hbound : ∀ i, P i ≤ C * (A (i + 1) - A i + kappa * (1 / 4 : ℝ) ^ i)) :
    Summable P ∧ (∑' i, P i) ≤ C * (omega - A 0 + kappa * (4 / 3)) :=
  ⟨volume_defect_summable hmono hupper hP hbound,
    volume_defect_tsum_le hC hkappa hupper hP hbound⟩

/-- The raw Euclidean-normalized volume profile can approach its density from
either side.  Its convergence is enough for the same defect budget; monotonicity
of that raw profile is not needed. -/
theorem volume_defect_budget_of_profile_limit {A P : ℕ → ℝ}
    {C kappa omega density : ℝ} (hC : 0 ≤ C)
    (hA : Tendsto A atTop (𝓝 density)) (hdensity : density ≤ omega)
    (hP : ∀ i, 0 ≤ P i)
    (hbound : ∀ i, P i ≤ C * (A (i + 1) - A i + kappa * (1 / 4 : ℝ) ^ i)) :
    Summable P ∧ (∑' i, P i) ≤ C * (omega - A 0 + kappa * (4 / 3)) := by
  have hgeom : Tendsto (fun k => ∑ i ∈ Finset.range k, (1 / 4 : ℝ) ^ i)
      atTop (𝓝 (4 / 3 : ℝ)) := by
    convert (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)).tendsto_sum_nat using 1
    norm_num
  have htotal : Tendsto (fun k => C *
      (A k - A 0 + kappa * ∑ i ∈ Finset.range k, (1 / 4 : ℝ) ^ i))
      atTop (𝓝 (C * (density - A 0 + kappa * (4 / 3)))) :=
    tendsto_const_nhds.mul
      ((hA.sub tendsto_const_nhds).add (tendsto_const_nhds.mul hgeom))
  have hfinite : ∀ k, (∑ i ∈ Finset.range k, P i) ≤
      C * (omega - A 0 + kappa * (4 / 3)) := by
    intro k
    have hlimit : (∑ i ∈ Finset.range k, P i) ≤
        C * (density - A 0 + kappa * (4 / 3)) := by
      apply ge_of_tendsto htotal
      filter_upwards [eventually_ge_atTop k] with j hj
      exact (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hj) (fun i _ _ => hP i)).trans
          (volume_defect_partial_sum_telescope hbound j)
    refine hlimit.trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact add_le_add (sub_le_sub_right hdensity (A 0)) le_rfl
  exact ⟨summable_of_sum_range_le hP hfinite,
    Real.tsum_le_of_sum_range_le hP hfinite⟩

/-- Vanishing initial volume deficit and rescaled curvature force the total
nonnegative defect to vanish along a sequence of rescalings. -/
theorem volume_defect_totals_tendsto_zero {P : ℕ → ℕ → ℝ}
    {initialVolume kappa : ℕ → ℝ} {C omega : ℝ}
    (hvolume : Tendsto initialVolume atTop (𝓝 omega))
    (hkappa : Tendsto kappa atTop (𝓝 0)) (hP : ∀ nu i, 0 ≤ P nu i)
    (hbudget : ∀ nu, (∑' i, P nu i) ≤
      C * (omega - initialVolume nu + kappa nu * (4 / 3))) :
    Tendsto (fun nu => ∑' i, P nu i) atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun nu => C * (omega - initialVolume nu + kappa nu * (4 / 3)))
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul
      ((tendsto_const_nhds.sub hvolume).add (hkappa.mul_const (4 / 3))) using 1
    simp
  exact squeeze_zero (fun nu => tsum_nonneg (hP nu)) hbudget hmajor

end RegularPointCoordinates

end OAI
