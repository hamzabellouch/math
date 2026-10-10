import OAI.NumberTheory.Jacobsthal.Paths.FirstVisitRatioTail

namespace OAI

namespace Erdos970


open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.OccupationDecomposition NumberTheoryLean.InitialOccupation
open NumberTheoryLean.CostPrefixTransport NumberTheoryLean.EvenBandBounds
open Erdos970Dependency.StateKernelInvariance

theorem full_band_tail_bound (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧ ∃ U : ℝ, 4 ≤ U ∧
    ∀ T : ℝ, U ≤ T → ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 →
      fullOccupation (.inl s,0) (highBand T v h) ≤
        ENNReal.ofReal (Real.exp (-2*(T-(U-1)))) + C*stateMeasure (highStates T) := by
  obtain ⟨C,hC,hlater⟩ := later_band_tail_bound h
  obtain ⟨U,hU,hfirst⟩ := first_band_tail_bound
  refine ⟨C,hC,U,hU,?_⟩
  intro T hT v s hsL hsU
  rw [fullOccupation_first_and_later]
  change costKernel (.inl s,0) (highBand T v h) +
      prefixOccupation 2 (.inl s,0) (highBand T v h) ≤ _
  exact add_le_add (hfirst T hT v h s hsU) (hlater T v s hsL hsU)

theorem uniform_full_occupation_tail (h eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 →
      fullOccupation (.inl s,0) (highBand T v h) ≤ ENNReal.ofReal eps := by
  obtain ⟨C,hC,U,_hU,hb⟩ := full_band_tail_bound h
  have hct : Tendsto (fun T : ℝ => C*stateMeasure (highStates T)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul stateMeasure_tail_tendsto (Or.inr hC.ne)
  have ht : Tendsto (fun T : ℝ => ENNReal.ofReal (Real.exp (-2*(T-(U-1)))) +
      C*stateMeasure (highStates T)) atTop (𝓝 0) := by
    simpa only [add_zero] using (exponential_tail_tendsto U).add hct
  have hsmall := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr heps))
  filter_upwards [hsmall,eventually_ge_atTop U] with T hT hU
  intro v s hsL hsU
  exact (hb T hU v s hsL hsU).trans hT.le

theorem exists_full_occupation_threshold (h eps : ℝ) (heps : 0 < eps) :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 →
      fullOccupation (.inl s,0) (highBand T v h) ≤ ENNReal.ofReal eps := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (uniform_full_occupation_tail h eps heps)
  refine ⟨max T₀ 3,le_max_right _ _,?_⟩
  intro T hT
  exact hT₀ T ((le_max_left _ _).trans hT)

end ErdosHighRatioBandTail


end Erdos970

end OAI
