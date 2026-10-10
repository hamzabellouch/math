import OAI.Geometry.RCD.Metric.ModelVolumeComparison
import OAI.Geometry.RCD.Metric.VolumeDensity
import Mathlib.Topology.Order.Monotone

namespace OAI

/-! # The positive finite small-scale volume density

The model-normalized volume ratio has a positive finite limit at every
point.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.volume_density_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ euclideanUnitVolume n ∧
      ∀ s : ℕ → ℝ, (∀ k, 0 < s k) → Tendsto s atTop (𝓝 0) →
        Tendsto (fun k => (hausdorff n X).real (ball p (s k)) / (s k)^n)
          atTop (𝓝 θ) := by
  obtain ⟨a,ha,hBG⟩ := hX.exists_model_ballVolumeComparison hn
  let M := comparisonModelVolume (n-1) a
  have hM (r : ℝ) (hr : 0 < r) : 0 < M r := comparisonModelVolume_pos (n-1) ha hr
  let f := fun r => (hausdorff n X).real (ball p r) / M r
  have hf : AntitoneOn f (Ioi 0) := by
    intro r hr R hR hrR
    exact (div_le_div_iff₀ (hM R hR) (hM r hr)).mpr (hBG p r R hr hrR)
  have hupper (r : ℝ) (hr : 0 < r) : f r ≤ euclideanUnitVolume n := by
    apply (div_le_iff₀ (hM r hr)).mpr
    exact volume_upper_of_small_scale_upper hBG hM (hX.smallScaleVolumeUpper hn ha p) hr
  have hbdd : BddAbove (f '' Ioi 0) := ⟨euclideanUnitVolume n,by
    rintro _ ⟨r,hr,rfl⟩
    exact hupper r hr⟩
  let θ := sSup (f '' Ioi 0)
  have hnon : (f '' Ioi 0).Nonempty := ⟨f 1,1,by norm_num,rfl⟩
  have hθ : 0 < θ := lt_of_lt_of_le (show 0 < f 1 from div_pos
    (ENNReal.toReal_pos (hX.fullSupport p 1 (by norm_num)).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) (hM 1 (by norm_num)))
    (le_csSup hbdd (mem_image_of_mem f (by norm_num : (0:ℝ)<1)))
  refine ⟨θ,hθ,csSup_le hnon (by rintro _ ⟨r,hr,rfl⟩; exact hupper r hr),?_⟩
  intro s hs hs0
  have hsgt : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs0,Eventually.of_forall hs⟩
  have hflim : Tendsto (fun k => f (s k)) atTop (𝓝 θ) :=
    (hf.tendsto_nhdsGT hbdd).comp hsgt
  have hnid : n-1+1=n := by omega
  have hb (k : ℕ) : 0 ≤ M (s k)/(s k)^n-1 ∧
      M (s k)/(s k)^n-1 ≤ Real.cosh (a*s k)^(n-1)-1 := by
    simpa only [hnid] using comparisonModelVolume_relative_error (n-1) ha (hs k) le_rfl
  have hcosh : Tendsto (fun k => Real.cosh (a*s k)^(n-1)-1) atTop (𝓝 0) := by
    simpa using ((((Real.continuous_cosh.tendsto 0).comp
      (by simpa using hs0.const_mul a)).pow (n-1)).sub_const 1)
  have hratio0 := squeeze_zero (fun k => (hb k).1) (fun k => (hb k).2) hcosh
  have hratio : Tendsto (fun k => M (s k)/(s k)^n) atTop (𝓝 1) := by
    simpa only [sub_add_cancel,zero_add] using hratio0.add_const 1
  have hproduct := hflim.mul hratio
  simpa only [f,div_mul_div_cancel₀ (hM _ (hs _)).ne',mul_one] using hproduct

end RegularPointCoordinates

end

end OAI
