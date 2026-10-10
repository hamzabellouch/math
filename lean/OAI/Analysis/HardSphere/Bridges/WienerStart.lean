import Mathlib
import OAI.Analysis.HardSphere.Geometry.KilledObservable

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener

lemma wiener_start_zero : ∀ᵐ w ∂wiener, w (0:Time)=0 := by
  rw [wiener, ae_map_iff measurable_path.aemeasurable
    ((isClosed_eq (continuous_eval_const (0:Time)) continuous_const).measurableSet)]
  exact Eventually.of_forall path_at_zero

lemma coordinateWiener_start_zero (N : ℕ) :
    ∀ᵐ w ∂coordinateWiener N, ∀ p, w p (0:Time)=0 := by
  rw [ae_all_iff]
  intro p
  exact (measurePreserving_eval (fun _ : Direction N ↦ wiener) p).quasiMeasurePreserving.ae wiener_start_zero

lemma freeTrajectory_time_continuous (N : ℕ) (L : Length)
    (w : CoordinatePaths N) (X : Configuration N L) :
    Continuous (fun t : ℝ ↦ freeTrajectory N L t w X) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  unfold Function.uncurry
  change Continuous (fun p : ℝ × Time ↦ fun i j ↦
    X i j + ((Real.sqrt (2*p.1)*w (i,j) p.2 : ℝ) : AddCircle L.val))
  fun_prop

@[simp] lemma freeTrajectory_zero (N : ℕ) (L : Length)
    (w : CoordinatePaths N) (X : Configuration N L) :
    freeTrajectory N L 0 w X=ContinuousMap.const Time X := by
  ext t i j
  simp [freeTrajectory]

lemma freeTrajectory_start (N : ℕ) (L : Length) (t : ℝ)
    {w : CoordinatePaths N} (hw : ∀ p, w p (0:Time)=0) (X : Configuration N L) :
    freeTrajectory N L t w X 0=X := by
  ext i j
  simp [freeTrajectory,hw]

lemma freeTrajectory_allowed_eventually (N : ℕ) (L : Length) (a : ℝ)
    (w : CoordinatePaths N) {X : Configuration N L} (hX : X∈allowed N L a) :
    ∀ᶠ t : ℝ in 𝓝 0, freeTrajectory N L t w X∈staysAllowed N L a := by
  have hc := (freeTrajectory_time_continuous N L w X).continuousAt (x := 0)
  apply hc.preimage_mem_nhds
  apply (staysAllowed_open N L a).mem_nhds
  rw [freeTrajectory_zero]
  rintro _ ⟨t,rfl⟩
  exact hX

lemma killedObservable_tendsto_zero (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) {w : CoordinatePaths N}
    (hw : ∀ p, w p (0:Time)=0) (X : Configuration N L) :
    Tendsto (fun t : ℝ ↦ killedObservable N L a g (freeTrajectory N L t w X))
      (𝓝 0) (𝓝 ((allowed N L a).indicator g X)) := by
  by_cases hX : X∈allowed N L a
  · rw [Set.indicator_of_mem hX]
    have ht := (g.continuous.comp ((continuous_eval_const (1:Time)).comp
      (freeTrajectory_time_continuous N L w X))).tendsto (0:ℝ)
    simp only [Function.comp_def, freeTrajectory_zero, ContinuousMap.const_apply] at ht
    apply ht.congr'
    filter_upwards [freeTrajectory_allowed_eventually N L a w hX] with t ht
    simp only [killedObservable,Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem hX]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0:ℂ)) (𝓝 0) (𝓝 0)) using 1
    funext t
    apply Set.indicator_of_notMem
    intro h
    exact hX ((freeTrajectory_start N L t hw X) ▸ h (Set.mem_range_self 0))

lemma killedAverage_tendsto_zero (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) (X : Configuration N L) :
    Tendsto (fun t : ℝ ↦ killedAverage N L a t g X)
      (𝓝 0) (𝓝 ((allowed N L a).indicator g X)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖g‖)
    (μ := coordinateWiener N)
    (F := fun t w ↦ killedObservable N L a g (freeTrajectory N L t w X))
    (f := fun _ ↦ (allowed N L a).indicator g X)
    (Eventually.of_forall fun t ↦ ((killedObservable_measurable N L a g.continuous.measurable).comp
      ((freeTrajectory_continuous N L t).comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable)
    (Eventually.of_forall fun _ ↦ Eventually.of_forall fun _ ↦
      killedObservable_bound N L a (norm_nonneg g) g.norm_coe_le_norm _)
    (integrable_const _)
    ((coordinateWiener_start_zero N).mono fun w hw ↦ killedObservable_tendsto_zero N L a g hw X)
  simpa only [killedAverage,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using h

end HardSphere

end

end OAI
