import OAI.GroupTheory.PolycyclicRecognition.Analysis.OrbitAverageIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

/-! # The mass identified by a convergent convex orbit average -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {G X : Type*} [Group G] [MeasurableSpace X]
  [MulAction G X] [MeasurableConstSMul G X]
  (ν : Measure X) [IsFiniteMeasure ν] [SMulInvariantMeasure G X ν]

theorem orbitAverage_limit_mass (f : X → ℝ) (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ 1)
    (A : ℕ → FiniteOrbitAverage G) (c : ℝ)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => (A n).apply f x) atTop (𝓝 c)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂ν) = ENNReal.ofReal c * ν univ := by
  have ht := tendsto_lintegral_of_dominated_convergence
    (μ := ν) (fun _ : X => (1 : ℝ≥0∞))
    (fun n => ENNReal.measurable_ofReal.comp ((A n).measurable_apply f hf))
    (fun n => Filter.Eventually.of_forall (fun x => by
      simpa using ENNReal.ofReal_le_ofReal ((A n).apply_le_one f hb x)))
    (by simp)
    (hlim.mono (fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx))
  change Tendsto (fun n => ∫⁻ x, ENNReal.ofReal ((A n).apply f x) ∂ν)
    atTop (𝓝 (∫⁻ _ : X, ENNReal.ofReal c ∂ν)) at ht
  simp_rw [FiniteOrbitAverage.lintegral ν _ f hf hn] at ht
  simp only [lintegral_const] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

theorem orbitAverage_indicator_limit_mass (t : Set X) (ht : MeasurableSet t)
    (A : ℕ → FiniteOrbitAverage G) (c : ℝ)
    (hlim : ∀ᵐ x ∂ν,
      Tendsto (fun n => (A n).apply (t.indicator (fun _ => (1 : ℝ))) x) atTop (𝓝 c)) :
    ν t = ENNReal.ofReal c * ν univ := by
  have hm := orbitAverage_limit_mass ν (t.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator ht)
    (fun x => by by_cases hx : x ∈ t <;> simp [hx])
    (fun x => by by_cases hx : x ∈ t <;> simp [hx]) A c hlim
  have he : (fun x => ENNReal.ofReal (t.indicator (fun _ => (1 : ℝ)) x)) =
      t.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ t <;> simp [hx]
  rw [he, lintegral_indicator ht] at hm
  simpa using hm

end PolycyclicRecognition

end

end OAI
