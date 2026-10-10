import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Pushforward

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u
namespace CurrentOperations
attribute [local instance] Classical.propDecidable
variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in

lemma pushCurrent_boundarySucc {k : ℕ} (T : Functional X (k+1))
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    boundarySucc (pushCurrent f T) = pushCurrent f (boundarySucc T) := by
  funext b π
  by_cases h : Admissible b π
  · have hcons : Admissible (fun _ : Y => (1 : ℝ)) (Matrix.vecCons b π) := by
      refine ⟨BoundedLip.const 1, ?_⟩
      intro i
      refine Fin.cases h.1.1 (fun j => h.2 j) i
    rw [boundarySucc, ite_eq_left h, pushCurrent_apply f T hcons,
      pushCurrent_apply f (boundarySucc T) h, boundarySucc,
      ite_eq_left (admissible_comp h hf)]
    congr 1
    funext i x
    exact Fin.cases rfl (fun _ => rfl) i
  · simp only [boundarySucc, pushCurrent, ite_eq_right h]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_zero {k : ℕ} (f : X → Y) :
    pushCurrent f (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = 0 := by
  funext b π
  simp only [pushCurrent, ite_self, Pi.zero_apply]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_cycle {k : ℕ} {T : Functional X (k+1)}
    (hT : boundarySucc T = 0) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    boundarySucc (pushCurrent f T) = 0 := by
  rw [pushCurrent_boundarySucc T hf, hT]
  exact pushCurrent_zero f

lemma mass_pushCurrent_le [CompactSpace X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    mass (pushCurrent f T) ≤ (K : ℝ)^k * mass T := by
  obtain ⟨μ, hμ, hc, hm⟩ := hT.exists_controls_mass_eq
  let := hμ
  have hfin : IsFiniteMeasure ((↑(K^k) : ℝ≥0∞) • μ.map f) := by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (μ.map f) univ)
  calc
    mass (pushCurrent f T) ≤ (((↑(K^k) : ℝ≥0∞) • μ.map f)).real univ :=
      mass_le_measure hfin (pushCurrent_controls hT hc hf)
    _ = (K : ℝ)^k * mass T := by
      rw [hm]
      simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.coe_toReal, NNReal.coe_pow, Measure.map_apply hf.continuous.measurable
          MeasurableSet.univ, preimage_univ]

end CurrentOperations
end CAT0Fillings

end
end

end OAI
