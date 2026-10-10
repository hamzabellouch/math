import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ActualProfileCycleGain

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace YauCounterexamples
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma actualProfileMass_pos (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ Ω, coordinateMetricGradient g u x ≠ 0)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] (hμ : μ Ω ≠ 0) :
    0 < actualProfileMass g u μ Ω := by
  apply (integral_pos_iff_support_of_nonneg (actualProfileSpeed_nonneg g u)
    (integrableOn_actualProfileSpeed g hu hΩc μ)).mpr
  have hsub : Ω ⊆ Function.support (actualProfileSpeed g u) := by
    intro x hx
    exact ne_of_gt (actualCoordinateNorm_pos g x (ha x hx))
  have hh : 0 < (μ.restrict Ω) Ω := by simpa only [Measure.restrict_apply hΩm,inter_self] using pos_iff_ne_zero.mpr hμ
  exact hh.trans_le (measure_mono hsub)

theorem actual_metric_profile_iterate (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
      tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
      (1+actualProfileCycleGain)^n*actualProfileMass g u μ Ω ≤ actualProfileMass g v μ Ω := by
  induction n generalizing ε with
  | zero =>
    refine ⟨u,hu,?_,?_,?_,fun x hx => ⟨ha x hx,hstrict x hx⟩,?_⟩
    · dsimp [HasCompactSupport]; simp
    · simp
    · simpa using (fun _ : E => hε)
    · simp
  | succ n ih =>
    obtain ⟨v,hv,hvc,hvs,hv0,hvp,hvm⟩ := ih (half_pos hε)
    obtain ⟨w,hw,hwc,hws,hw0,hwp,hwm⟩ := actual_metric_profile_cycle hdim g hv hΩ hΩc
      (fun x hx => (hvp x hx).1) (fun x hx => (hvp x hx).2) μ (half_pos hε)
    refine ⟨w,hw,?_,?_,?_,hwp,?_⟩
    · have he : ((fun x => w x-v x)+(fun x => v x-u x)) = (fun x => w x-u x) := by
        funext x; dsimp; ring
      exact he ▸ hwc.add hvc
    · have hs := (tsupport_add (fun x => w x-v x) (fun x => v x-u x)).trans (union_subset hws hvs)
      simpa only [Pi.add_apply,sub_add_sub_cancel] using hs
    · intro x
      calc |w x-u x| = |(w x-v x)+(v x-u x)| := by congr 1; ring
        _ ≤ |w x-v x|+|v x-u x| := abs_add_le _ _
        _ < ε/2+ε/2 := add_lt_add (hw0 x) (hv0 x)
        _ = ε := by ring
    · have hh := mul_le_mul_of_nonneg_left hvm (show 0 ≤ 1+actualProfileCycleGain by linarith [actualProfileCycleGain_pos])
      rw [pow_succ]
      nlinarith only [hh,hwm]

theorem actual_metric_profile_amplification (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] (hμ : μ Ω ≠ 0)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
      tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
      T < actualProfileMass g v μ Ω := by
  have hM := actualProfileMass_pos g hu hΩ.measurableSet hΩc
    (fun x hx => ha x (subset_closure hx)) μ hμ
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (T/actualProfileMass g u μ Ω)
    (show 1 < 1+actualProfileCycleGain by linarith [actualProfileCycleGain_pos])
  obtain ⟨v,hv,hvc,hvs,hv0,hvp,hvm⟩ := actual_metric_profile_iterate hdim g hu hΩ hΩc ha hstrict μ n hε
  exact ⟨v,hv,hvc,hvs,hv0,hvp,((div_lt_iff₀ hM).mp hn).trans_le hvm⟩

end YauCounterexamples

end

end OAI
