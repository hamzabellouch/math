import OAI.Analysis.FiniteFactor.Sampling.SecondLevels
import OAI.Analysis.FiniteFactor.Sampling.IntervalSums

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- The interval endpoints depend only on the weight and level, and work
simultaneously for every atomless law carried by [0,1). -/
theorem samplingTestedSecond_level_exists (h α : ℝ) (G : Set ℝ) (a c s r : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hr : 0 < r) :
    ∃ A B : Fin 2 → ℝ, ∀ (ν : Measure ℝ) [NullSingletonClass ν],
      (∀ᵐ t ∂ν, t ∈ Set.Ico (0 : ℝ) 1) →
      (fun t => if r ≤ samplingTestedSecondWeight h α (Set.Icc a c) G s t then (1 : ℝ) else 0) =ᵐ[ν]
        (fun t => ∑ j, samplingClosedIndicator (A j) (B j) t) := by
  by_cases hG : s ∈ G
  · refine ⟨![max 0 (max (s-(1-α)) (s-c)),
        max (max (max 0 (max (s-(1-α)) (s-c))) (s-1/2)) (s-1/(h*r))],
      ![min (min (min (samplingSecondLength h s) (min (s-α) (s-a))) (s-1/2)) (s-1+1/(h*r)),
        min (samplingSecondLength h s) (min (s-α) (s-a))],?_⟩
    intro ν _ hν
    filter_upwards [hν,
      ae_iff.mpr (show ν {t | ¬t ≠ 0} = 0 by simp),
      ae_iff.mpr (show ν {t | ¬t ≠ samplingSecondLength h s} = 0 by simp),
      ae_iff.mpr (show ν {t | ¬t ≠ s-1/2} = 0 by simp)] with t ht ht0 htL htm
    simpa [Fin.sum_univ_two,samplingClosedIndicator,samplingSecondLevelLeft,samplingSecondLevelRight]
      using samplingTestedSecond_level_intervals h α G a c s r t hh hh1 hα hs ht hr hG ht0 htL htm
  · refine ⟨fun _ => 1,fun _ => 0,?_⟩
    intro ν _ _
    apply Eventually.of_forall
    intro t
    simp [samplingTestedSecondWeight,hG,not_le.mpr hr,samplingClosedIndicator]

end
end FiniteFactor

end OAI
