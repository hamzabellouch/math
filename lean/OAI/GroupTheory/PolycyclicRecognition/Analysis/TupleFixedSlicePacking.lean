import OAI.GroupTheory.PolycyclicRecognition.Analysis.FixedSlicePacking
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # Fixed-slice lower packing for correlated tuples

An ambient product ball pulls back to a product of fixed-slice balls.  The
set to be packed need not be a product set.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

theorem lower_count_rate_of_volume
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (A : ℕ → ℝ≥0∞) (N : ℕ → ℕ) (C : ℝ≥0∞) (hC : C ≠ ⊤) {p : ℝ}
    (hvol : HasSubexponentialLowerBoundSeq scale
      (fun n => (A n).toReal / Real.exp (scale n * p)))
    (hbound : ∀ n, A n ≤ (N n : ℝ≥0∞) * C) :
    HasSubexponentialLowerBoundSeq scale
      (fun n => (N n : ℝ) / Real.exp (scale n * p)) := by
  have hc : 0 < C.toReal + 1 := by positivity
  apply (hvol.div (sequence_subexponential_upper_const hs (C.toReal + 1))
    (Eventually.of_forall (fun _ => hc))).mono
  apply Eventually.of_forall
  intro n
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) hC) (hbound n)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hb
  dsimp only
  rw [div_right_comm]
  apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
  apply (div_le_iff₀ hc).mpr
  have hN : 0 ≤ (N n : ℝ) := Nat.cast_nonneg _
  nlinarith

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [TopologicalSpace N] [MeasurableSpace N] [MeasurableMul N]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (μ : Measure N) [SigmaFinite μ] [μ.IsMulLeftInvariant]

omit [TopologicalSpace N] [IsTopologicalGroup G] in
theorem tuple_fixedSlice_ball_measure {h : ℕ}
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (x : Fin h → G) (d : Fin h → D) (v : Fin h → N) {r : ℝ} (hr : 0 ≤ r) :
    (Measure.pi fun _ : Fin h => μ)
      ((fun u : Fin h → N => fun i => x i * ι (u i) * κ (d i)) ⁻¹'
        closedBall (fun i => x i * ι (v i) * κ (d i)) r) =
      μ (ι ⁻¹' closedBall (1 : G) r) ^ h := by
  have he : (fun u : Fin h → N => fun i => x i * ι (u i) * κ (d i)) ⁻¹'
      closedBall (fun i => x i * ι (v i) * κ (d i)) r =
      Set.pi univ (fun i =>
        (fun u : N => x i * ι u * κ (d i)) ⁻¹' closedBall (x i * ι (v i) * κ (d i)) r) := by
    ext u
    simp only [mem_preimage, mem_closedBall, dist_pi_le_iff hr, Set.mem_pi, mem_univ,
      forall_const]
  rw [he, Measure.pi_pi]
  simp_rw [fixedSlice_ball_measure ι κ φ μ hφ hconj]
  simp

theorem exists_tuple_fixedSlice_separated_net {h : ℕ}
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Continuous ι) (x : Fin h → G) (d : Fin h → D)
    {S : Set (Fin h → N)} (hS : IsCompact S) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset (Fin h → G),
      (↑t : Set (Fin h → G)) ⊆ (fun u => fun i => x i * ι (u i) * κ (d i)) '' S ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → r < dist a b) ∧
      (Measure.pi fun _ : Fin h => μ) S ≤
        (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) ^ h := by
  apply exists_separated_image_net_volume_bound (Measure.pi fun _ : Fin h => μ) _
    (hS.image (continuous_pi (fun i =>
      (continuous_const.mul (hι.comp (continuous_apply i))).mul continuous_const))).totallyBounded hr
  rintro y ⟨v, _, rfl⟩
  exact (tuple_fixedSlice_ball_measure ι κ φ μ hφ hconj x d v hr.le).le

theorem exists_tuple_fixedSlice_count_rate {h : ℕ} [ProperSpace G]
    [IsFiniteMeasureOnCompacts μ]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hι : Topology.IsClosedEmbedding ι)
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (x : ℕ → Fin h → G) (d : ℕ → Fin h → D)
    (S : ℕ → Set (Fin h → N)) (hS : ∀ n, IsCompact (S n))
    {p : ℝ} (hvol : HasSubexponentialLowerBoundSeq scale
      (fun n => ((Measure.pi fun _ : Fin h => μ) (S n)).toReal / Real.exp (scale n * p)))
    {r : ℝ} (hr : 0 < r) :
    ∃ t : ℕ → Finset (Fin h → G),
      (∀ n, (↑(t n) : Set (Fin h → G)) ⊆
        (fun u => fun i => x n i * ι (u i) * κ (d n i)) '' S n) ∧
      (∀ n, ∀ a ∈ t n, ∀ b ∈ t n, a ≠ b → r < dist a b) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * p)) := by
  choose t ht hsep hbound using fun n =>
    exists_tuple_fixedSlice_separated_net ι κ φ μ hφ hconj hι.continuous (x n) (d n) (hS n) hr
  refine ⟨t, ht, hsep, lower_count_rate_of_volume hs _ _ _ ?_ hvol hbound⟩
  exact ENNReal.pow_ne_top (fixedSlice_packing_constant_lt_top ι μ hι r).ne

end PolycyclicRecognition

end

end OAI
