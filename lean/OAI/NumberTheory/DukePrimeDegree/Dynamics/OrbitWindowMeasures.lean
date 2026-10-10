import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitAverageFunctions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-!
# Probability laws of finite orbit windows

A window law is the average of the actual iterated pushforwards of its
initial law. For an ergodic transformation, uniformly dominated initial
laws give weak convergence to the invariant probability, even for
varying window lengths.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

/-- `N + 1` orbit samples, so the probability law is defined also at
`N = 0`. -/
def orbitWindowMeasure (ν : Measure X) (T : X → X) (N : ℕ) : Measure X :=
  ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range (N + 1), ν.map (T^[k])

lemma orbitWindowMeasure_univ (ν : Measure X) [IsProbabilityMeasure ν]
    (T : X → X) (hT : Measurable T) (N : ℕ) :
    orbitWindowMeasure ν T N univ = 1 := by
  have hm (k : ℕ) : (ν.map (T^[k])) univ = 1 := by
    rw [Measure.map_apply (hT.iterate k) MeasurableSet.univ]
    simp
  simp only [orbitWindowMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply, hm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

def orbitWindowProbability (ν : ProbabilityMeasure X)
    (T : X → X) (hT : Measurable T) (N : ℕ) : ProbabilityMeasure X :=
  ⟨orbitWindowMeasure ν T N, ⟨orbitWindowMeasure_univ ν T hT N⟩⟩

/-- A measurable factor map commutes with the actual finite window law. -/
lemma orbitWindowMeasure_map {Y : Type*} [MeasurableSpace Y]
    (ν : Measure X) (S : X → X) (hS : Measurable S)
    (T : Y → Y) (hT : Measurable T) (P : X → Y) (hP : Measurable P)
    (hsem : Function.Semiconj P S T) (N : ℕ) :
    (orbitWindowMeasure ν S N).map P = orbitWindowMeasure (ν.map P) T N := by
  have hlin : (orbitWindowMeasure ν S N).map P =
      ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ •
        ∑ k ∈ Finset.range (N + 1), (ν.map (S^[k])).map P := by
    simp only [orbitWindowMeasure, ← Measure.mapₗ_apply_of_measurable hP,
      map_smul, map_sum]
  rw [hlin, orbitWindowMeasure]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Measure.map_map hP (hS.iterate k), Measure.map_map (hT.iterate k) hP]
  congr 1
  funext x
  exact (hsem.iterate_right k) x

section Topological

variable [TopologicalSpace X] [OpensMeasurableSpace X]

lemma integral_orbitWindowMeasure (ν : Measure X) [IsProbabilityMeasure ν]
    (T : X → X) (hT : Measurable T) (N : ℕ) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂orbitWindowMeasure ν T N) =
      ∫ x, birkhoffAverage ℝ T f (N + 1) x ∂ν := by
  have hint (k : ℕ) : Integrable (fun x => f (T^[k] x)) ν :=
    (f.integrable (μ := ν.map (T^[k]))).comp_measurable (hT.iterate k)
  rw [orbitWindowMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun k _ => f.integrable (μ := ν.map (T^[k])))]
  simp_rw [integral_map (f := fun x => f x) (hT.iterate _).aemeasurable
    f.continuous.aestronglyMeasurable]
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  rw [integral_const_mul, integral_finsetSum (Finset.range (N + 1)) (fun k _ => hint k)]
  simp [ENNReal.toReal_add]

/-- Actual orbit-window laws converge weakly. No generic-point or
empirical-measure convergence premise is added. -/
theorem orbitWindowProbability_tendsto
    (μ : ProbabilityMeasure X) (T : X → X) (hT : Ergodic T (μ : Measure X))
    (ν : ℕ → ProbabilityMeasure X) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ n, (ν n : Measure X) ≤ ENNReal.ofReal C • (μ : Measure X))
    (length : ℕ → ℕ) (hlength : Tendsto length atTop atTop) :
    Tendsto (fun n => orbitWindowProbability (ν n) T
      hT.toMeasurePreserving.measurable (length n))
      atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hf : MemLp (fun x => f x) 2 (μ : Measure X) :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (ae_of_all _ f.norm_coe_le_norm)
  have hlen : Tendsto (fun n => length n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (length n)) hlength
  have hav := variable_orbit_average_tendsto_integral (μ : Measure X) T hT
    (fun x => f x) hf (fun n => (ν n : Measure X)) C hC hdom
    (fun n => length n + 1) hlen
  change Tendsto (fun n => ∫ x, f x ∂orbitWindowMeasure (ν n) T (length n))
    atTop (𝓝 (∫ x, f x ∂(μ : Measure X)))
  simp_rw [integral_orbitWindowMeasure (ν := (ν _ : Measure X)) T
    hT.toMeasurePreserving.measurable]
  exact hav

end Topological
end DukePrimeDegree

end

end OAI
