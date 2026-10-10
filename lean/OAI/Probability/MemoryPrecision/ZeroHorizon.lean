import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.RealStream

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression NoiselessRegression.Learner

lemma estimate_zero {d M : ℕ} {Ω : Type u} (L : Learner d M 0 Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d 0) :
    L.estimate s ω x = L.output 0 ω (L.initialChoice ω).2 := by
  by_cases h : (L.initialChoice ω).1 = true <;> simp [estimate, terminal, run, start, h]

lemma frozen_chord_zero {d M : ℕ} {Ω : Type u} (L : Learner d M 0 Ω)
    (ω : Ω) (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ((uniformSphere d).prod (sampleLaw d 0))
      {z | dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε} ≤
      ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  let : NeZero d := ⟨by omega⟩
  let y := (L.output 0 ω (L.initialChoice ω).2).val
  simp_rw [estimate_zero]
  change ((uniformSphere d).prod (sampleLaw d 0))
    (Prod.fst ⁻¹' {s : UnitSphere d | dist s.val y ≤ ε}) ≤ _
  rw [measurePreserving_fst.measure_preimage
    (measurableSet_le (measurable_subtype_coe.dist measurable_const) measurable_const).nullMeasurableSet]
  have h := ambientSphereLaw_closedBall (E := Space d) y hε (d-1) (by simp)
  rw [ambientSphereLaw, Measure.map_apply measurable_subtype_coe Metric.isClosed_closedBall.measurableSet] at h
  simpa [uniformSphere, sphereLaw, ENNReal.ofReal_mul, finrank_euclideanSpace_fin,
    Metric.closedBall, Set.preimage_ofPred_eq] using h

lemma chord_zero_bound {d M : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M 0 Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    uniformChordSuccess L ρ ε ≤ ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  let : NeZero d := ⟨by omega⟩
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d 0) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d 0) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d 0) |
    dist (L.estimate z.1 z.2.1 z.2.2).val z.1.val ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d 0))) :=
    nullMeasurableSet_le
      ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).dist
        (measurable_subtype_coe.comp measurable_fst).aemeasurable) aemeasurable_const
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)))
    (by
      filter_upwards [] with ω
      change ((uniformSphere d).prod (sampleLaw d 0))
        {z | dist (L.estimate z.1 ω z.2).val z.1.val ≤ ε} ≤ _
      simpa only [dist_comm] using frozen_chord_zero L ω hd hε)
  simpa only [he, measure_univ, mul_one, S, uniformChordSuccess] using hb

lemma angular_event_subset_chord {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ε : ℝ) :
    {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} ⊆
    {z | dist (L.estimate z.1 z.2.1 z.2.2).val z.1.val ≤ ε} := by
  intro z hz
  exact le_trans (chord_le_arccos (L.estimate z.1 z.2.1 z.2.2) z.1) hz
lemma angular_le_chord {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) :
    L.uniformSuccess ρ ε ≤ uniformChordSuccess L ρ ε :=
  measure_mono (angular_event_subset_chord L ε)
end MemoryPrecision


end

end OAI
