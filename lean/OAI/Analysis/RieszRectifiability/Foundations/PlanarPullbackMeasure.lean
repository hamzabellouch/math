import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.OrthogonalNormalFrame
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

/-!
Pullback along the adjoint of an isometric embedding transports a measure supported on
its range to Euclidean coordinates, preserving ball masses and upper growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def planarPullbackMeasure {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) : Measure (Ambient n) := ν.map L.toContinuousLinearMap.adjoint

theorem planarPullbackMeasure_recover {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d))) :
    (planarPullbackMeasure L ν).map L = ν := by
  rw [planarPullbackMeasure, Measure.map_map L.continuous.measurable
    L.toContinuousLinearMap.adjoint.continuous.measurable]
  have heq : (fun x => L (L.toContinuousLinearMap.adjoint x)) =ᵐ[ν] id := by
    filter_upwards [ν.support_mem_ae] with x hx
    obtain ⟨y, hy⟩ := hs hx
    change L y = x at hy
    rw [← hy]
    have hleft : L.toContinuousLinearMap.adjoint (L y) = y := DFunLike.congr_fun L.adjoint_comp_self y
    simp only [id_eq, hleft]
  exact (Measure.map_congr heq).trans Measure.map_id

theorem planarPullbackMeasure_ball {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (x : Ambient n) (r : ℝ) : planarPullbackMeasure L ν (ball x r) = ν (ball (L x) r) := by
  rw [planarPullbackMeasure, Measure.map_apply L.toContinuousLinearMap.adjoint.continuous.measurable
    measurableSet_ball]
  apply measure_congr
  filter_upwards [ν.support_mem_ae] with y hy
  obtain ⟨z, hz⟩ := hs hy
  change L z = y at hz
  rw [← hz]
  have hleft : L.toContinuousLinearMap.adjoint (L z) = z := DFunLike.congr_fun L.adjoint_comp_self z
  apply propext
  change dist (L.toContinuousLinearMap.adjoint (L z)) x < r ↔ dist (L z) (L x) < r
  rw [hleft, L.dist_map]

theorem planarPullbackMeasure_growth {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C : ℝ) (hg : GlobalUpperGrowth n C ν) : GlobalUpperGrowth n C (planarPullbackMeasure L ν) := by
  refine ⟨hg.1, ?_⟩
  intro x r hr
  rw [planarPullbackMeasure_ball L ν hs]
  exact hg.2 (L x) r hr

theorem globalGrowth_finite_on_compacts {n d : ℕ} (C : ℝ)
    (ν : Measure (Ambient d)) (hg : GlobalUpperGrowth n C ν) : IsFiniteMeasureOnCompacts ν := by
  let : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (hg.2 x 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩⟩
  infer_instance

theorem planarPullbackMeasure_support_iff {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (x : Ambient n) : x ∈ (planarPullbackMeasure L ν).support ↔ L x ∈ ν.support := by
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [planarPullbackMeasure_ball L ν hs]

theorem planarPullbackMeasure_lower {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C : ℝ) (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r)) :
    ∀ x ∈ (planarPullbackMeasure L ν).support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ planarPullbackMeasure L ν (ball x r) := by
  intro x hx r hr
  rw [planarPullbackMeasure_ball L ν hs]
  exact hlower (L x) ((planarPullbackMeasure_support_iff L ν hs x).mp hx) r hr

theorem planarPullbackMeasure_ne_zero {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (hne : ν ≠ 0) : planarPullbackMeasure L ν ≠ 0 := by
  intro hz
  apply hne
  rw [← planarPullbackMeasure_recover L ν hs, hz, Measure.map_zero]

end

end RieszRectifiability

end OAI
