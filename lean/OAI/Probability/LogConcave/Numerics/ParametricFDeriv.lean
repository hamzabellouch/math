import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.CompactIntegral
open Set Function Filter MeasureTheory Metric
open scoped Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma parametric_hasFDerivAt {f : E × ℝ → F} (hf : ContDiff ℝ 1 f)
    {s : Set ℝ} (hs : IsCompact s) (x : E) :
    HasFDerivAt (fun x => ∫t in s,f (x,t))
      (∫t in s,(fderiv ℝ f (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D := fun p : E × ℝ => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := (hf.continuous_fderiv (by norm_num)).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hs).exists_bound_of_continuousOn hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F':=fun y t => D (y,t)) (bound:=fun _ => C) (ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall fun y => (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hs
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hs.measurableSet] with t ht y hy
    exact hC (y,t) ⟨ball_subset_closedBall hy,ht⟩
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards [] with t y _hy
    exact ((hf.differentiable (by norm_num) (y,t)).hasFDerivAt).comp y
      ((hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const (𝕜:=ℝ) t y))

theorem contDiff_parametric {f : E × ℝ → F} (n : ℕ)
    (hf : ContDiff ℝ (n:WithTop ℕ∞) f) {s : Set ℝ} (hs : IsCompact s) :
    ContDiff ℝ (n:WithTop ℕ∞) (fun x => ∫t in s,f (x,t)) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (continuous_parametric_integral_of_continuous (f:=fun x t => f (x,t)) hf.continuous hs)
  | succ n ih =>
    let D := fun p : E × ℝ => (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ (n:WithTop ℕ∞) D := (hf.fderiv_right (by simp)).clm_comp contDiff_const
    have hd (x : E) := parametric_hasFDerivAt (hf.of_le (by exact_mod_cast Nat.succ_pos n)) hs x
    rw [show ((n+1:ℕ):WithTop ℕ∞)=(n:WithTop ℕ∞)+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt,?_⟩
    refine ⟨by simp,?_⟩
    have he : fderiv ℝ (fun x => ∫t in s,f (x,t))=fun x => ∫t in s,D (x,t) := funext fun x => (hd x).fderiv
    rw [he]
    exact ih hD

theorem smooth_parametric {f : E × ℝ → F} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    {s : Set ℝ} (hs : IsCompact s) :
    ContDiff ℝ (⊤:ℕ∞) (fun x => ∫t in s,f (x,t)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_parametric n (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hs
end LogConcaveSampling.CompactIntegral

end

end

end

end OAI
