import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace OAI

/-!
# Selecting one map that is good on a finite mesh

The stationary volume comparison samples endpoints independently of the
stationary map. Uniform `L²` bounds at finitely many sampled path points
give a single map for which most endpoints have every sampled error small.
The finite mesh is fixed before the scale tends to infinity.
-/

namespace PolycyclicRecognition

open MeasureTheory
open scoped ENNReal

/-- Chebyshev and the finite union bound for a fixed mesh. -/
theorem measure_bad_mesh_le
    {I Z E : Type*} [Fintype I] [MeasurableSpace Z] [NormedAddCommGroup E]
    (μ : Measure Z) (f : I → Z → E) {η a : ℝ≥0∞}
    (hη : η ≠ 0) (hηtop : η ≠ ∞)
    (hbound : ∀ i, eLpNorm (f i) 2 μ ≤ a) :
    μ {z | ∃ i, η ≤ ‖f i z‖ₑ} ≤ (Fintype.card I : ℝ≥0∞) * (η⁻¹ ^ 2 * a ^ 2) := by
  have hbad : {z | ∃ i, η ≤ ‖f i z‖ₑ} = ⋃ i, {z | η ≤ ‖f i z‖ₑ} := by
    ext z
    simp
  rw [hbad]
  calc
    μ (⋃ i, {z | η ≤ ‖f i z‖ₑ}) ≤ ∑ i, μ {z | η ≤ ‖f i z‖ₑ} :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : I, η⁻¹ ^ 2 * a ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := meas_ge_le_mul_pow_eLpNorm_enorm (p := 2) μ (by norm_num)
        (by norm_num) (f := f i) hη (fun h => (hηtop h).elim)
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
      apply h.trans
      gcongr
      exact hbound i
    _ = _ := by simp [nsmul_eq_mul]

/-- A set of small product measure has a small fiber over some point of a
probability space. This selects the map after endpoint averaging. -/
theorem exists_fiber_measure_lt
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [SFinite ν]
    (s : Set (X × Y)) (hs : MeasurableSet s) {t : ℝ≥0∞}
    (hsmall : (μ.prod ν) s < t) :
    ∃ x, ν {y | (x, y) ∈ s} < t := by
  by_contra h
  push Not at h
  have hi : t ≤ ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ := by
    calc
      t = ∫⁻ _x, t ∂μ := by simp
      _ ≤ _ := lintegral_mono h
  rw [Measure.prod_apply hs] at hsmall
  exact (not_le_of_gt hsmall) hi

/-- Uniform `L²` estimates at each sampled point provide one stationary map
with an exceptional endpoint set of arbitrarily prescribed small measure. -/
theorem exists_good_mesh_fiber
    {I X Y E : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : I → X × Y → E) (hf : ∀ i, Measurable (f i))
    {η a t : ℝ≥0∞} (hη : η ≠ 0) (hηtop : η ≠ ∞)
    (hbound : ∀ i y, eLpNorm (fun x => f i (x, y)) 2 μ ≤ a)
    (hsmall : (Fintype.card I : ℝ≥0∞) * (η⁻¹ ^ 2 * a ^ 2) < t) :
    ∃ x, ν {y | ∃ i, η ≤ ‖f i (x, y)‖ₑ} < t := by
  let s : Set (X × Y) := {z | ∃ i, η ≤ ‖f i z‖ₑ}
  have hs : MeasurableSet s := by
    have heq : s = ⋃ i, {z | η ≤ ‖f i z‖ₑ} := by ext z; simp [s]
    rw [heq]
    exact MeasurableSet.iUnion (fun i => measurableSet_le measurable_const (hf i).enorm)
  apply exists_fiber_measure_lt μ ν s hs
  apply lt_of_le_of_lt _ hsmall
  rw [Measure.prod_apply_symm hs]
  calc
    (∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν) ≤
        ∫⁻ _y, (Fintype.card I : ℝ≥0∞) * (η⁻¹ ^ 2 * a ^ 2) ∂ν := by
      apply lintegral_mono
      intro y
      exact measure_bad_mesh_le μ (fun i x => f i (x, y)) hη hηtop (fun i => hbound i y)
    _ = _ := by simp

end PolycyclicRecognition

end OAI
