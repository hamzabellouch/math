import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.SignedVariationFinite

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma measureReal_sub (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ν ≤ μ) : (μ-ν).real univ = μ.real univ-ν.real univ := by
  rw [measureReal_def,Measure.sub_apply MeasurableSet.univ h,
    ENNReal.toReal_sub_of_le (h univ) (measure_ne_top μ univ)]
  rfl
lemma monotone_limit_le (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (hmono : Antitone (fun n => (α n : Measure ℝ)))
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun N => (α N : Measure ℝ) s) atTop
      (𝓝 ((αinf : Measure ℝ) s))) (n : ℕ) : (αinf : Measure ℝ) ≤ (α n : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro s hs
  apply le_of_tendsto (hlim s hs)
  filter_upwards [eventually_ge_atTop n] with N hN
  exact hmono hN s
lemma monotone_drop_mass_summable (α : ℕ → FiniteMeasure ℝ)
    (hmono : Antitone (fun n => (α n : Measure ℝ))) :
    Summable (fun n => ((α n : Measure ℝ)-(α (n+1) : Measure ℝ)).real univ) := by
  have hm (n : ℕ) := measureReal_sub (α n : Measure ℝ) (α (n+1) : Measure ℝ) (hmono (Nat.le_succ n))
  apply summable_of_sum_range_le (c := (α 0 : Measure ℝ).real univ) (fun _ => ENNReal.toReal_nonneg)
  intro N
  change (∑ n ∈ Finset.range N, ((α n : Measure ℝ)-(α (n+1) : Measure ℝ)).real univ) ≤ _
  simp_rw [hm]
  rw [Finset.sum_range_sub']
  exact sub_le_self _ ENNReal.toReal_nonneg
lemma monotone_tail_mass_tendsto_zero (α : ℕ → FiniteMeasure ℝ) (αinf : FiniteMeasure ℝ)
    (hmono : Antitone (fun n => (α n : Measure ℝ)))
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun N => (α N : Measure ℝ) s) atTop
      (𝓝 ((αinf : Measure ℝ) s))) :
    Tendsto (fun n => ((α n : Measure ℝ)-(αinf : Measure ℝ)).real univ) atTop (𝓝 0) := by
  simp_rw [measureReal_sub _ _ (monotone_limit_le α αinf hmono hlim _)]
  have hh := ((ENNReal.tendsto_toReal (measure_ne_top (αinf : Measure ℝ) univ)).comp
    (hlim univ MeasurableSet.univ)).sub_const ((αinf : Measure ℝ).real univ)
  simpa only [measureReal_def,sub_self,Function.comp_def] using hh

end CurrentFalconer.MonotoneShell
end
end

end OAI
