import Mathlib
import OAI.Analysis.HardSphere.Geometry.ConfigurationPath

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace IndicatorStrong
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re]
  · congr 1
    ext x
    simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  · exact L2.integrable_inner f f

lemma tendsto_L2_of_norm_dominated {F : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ}
    (b : α → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖(F n - f) x‖^2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ (F n - f) x) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 f) := by
  have hs : Tendsto (fun n ↦ ‖F n - f‖^2) atTop (𝓝 0) := by
    simp_rw [norm_sq_integral]
    have hi := tendsto_integral_of_dominated_convergence b
      (fun n ↦ (show AEStronglyMeasurable (fun x ↦ ‖(F n - f) x‖^2) μ from (Lp.aestronglyMeasurable (F n - f)).norm.pow 2)) hb
      (fun n ↦ (hbound n).mono fun x hx ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖(F n - f) x‖))] using hx)
      (hlim.mono fun x hx ↦ by simpa using hx.norm.pow 2)
    simpa using hi
  have hn : Tendsto (fun n ↦ ‖F n - f‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma indicator_tendsto {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n))
    (hmono : Monotone S) (f : Lp ℂ 2 μ) :
    Tendsto (fun n ↦ ((Lp.memLp f).indicator (hS n)).toLp ((S n).indicator f))
      atTop (𝓝 (((Lp.memLp f).indicator (MeasurableSet.iUnion hS)).toLp ((⋃ n, S n).indicator f))) := by
  let F n := ((Lp.memLp f).indicator (hS n)).toLp ((S n).indicator f)
  let g := ((Lp.memLp f).indicator (MeasurableSet.iUnion hS)).toLp ((⋃ n, S n).indicator f)
  have hF n : F n =ᵐ[μ] (S n).indicator f := MemLp.coeFn_toLp _
  have hg : g =ᵐ[μ] (⋃ n, S n).indicator f := MemLp.coeFn_toLp _
  apply tendsto_L2_of_norm_dominated (fun x ↦ ‖f x‖^2)
    ((Lp.memLp f).integrable_norm_pow (by norm_num))
  · intro n
    filter_upwards [Lp.coeFn_sub (F n) g, hF n, hg] with x hx hfx hgx
    rw [hx, Pi.sub_apply, hfx, hgx]
    by_cases hn : x ∈ S n
    · have hu : x ∈ ⋃ n, S n := mem_iUnion.mpr ⟨n,hn⟩
      simp [hn,hu]
    · by_cases hu : x ∈ ⋃ n, S n <;> simp [hn,hu]
  · filter_upwards [ae_all_iff.mpr (fun n ↦ Lp.coeFn_sub (F n) g), ae_all_iff.mpr hF, hg]
      with x hx hfx hgx
    have heq n : (F n - g) x = (S n).indicator f x - (⋃ n, S n).indicator f x := by
      rw [hx n,Pi.sub_apply,hfx n,hgx]
    change Tendsto (fun n ↦ (F n - g) x) atTop (𝓝 (0:ℂ))
    simp_rw [heq]
    by_cases hu : x ∈ ⋃ n, S n
    · obtain ⟨n,hn⟩ := mem_iUnion.mp hu
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      simp [hmono hm hn, hu]
    · simpa only [Set.indicator_of_notMem hu, sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℂ)) atTop (𝓝 0)).congr'
          (Filter.Eventually.of_forall fun n ↦ by
            rw [Set.indicator_of_notMem (fun h ↦ hu (mem_iUnion.mpr ⟨n,h⟩))])

end IndicatorStrong

namespace HardSphere
open Wiener

lemma avoidanceMultiplier_innerRadius_tendsto (N : ℕ) (L : Length) (a t : ℝ)
    (f : FreePathL2 N L t) :
    Tendsto (fun n ↦ avoidanceMultiplier N L (innerRadius a n) t f) atTop
      (𝓝 (avoidanceMultiplier N L a t f)) := by
  have h := IndicatorStrong.indicator_tendsto
    (fun n ↦ (staysAllowed_open N L (innerRadius a n)).measurableSet)
    (fun m n hmn ↦ staysAllowed_antitone N L (innerRadius_antitone a hmn)) f
  simp only [staysAllowed_innerRadius] at h
  have heq (b : ℝ) : avoidanceMultiplier N L b t f =
      ((Lp.memLp f).indicator (staysAllowed_open N L b).measurableSet).toLp
        ((staysAllowed N L b).indicator f) := by
    apply Lp.ext
    exact (avoidanceMultiplier_ae N L b t f).trans (MemLp.coeFn_toLp _).symm
  simp_rw [← heq] at h
  exact h

lemma killedTransition_innerRadius_tendsto (N : ℕ) (L : Length) (a t : ℝ)
    (f : ScalarL2 N L) :
    Tendsto (fun n ↦ killedTransition N L (innerRadius a n) t f) atTop
      (𝓝 (killedTransition N L a t f)) := by
  exact ((endpointPull N L t 0).toContinuousLinearMap.adjoint.continuous.tendsto _).comp
    (avoidanceMultiplier_innerRadius_tendsto N L a t (endpointPull N L t 1 f))

end HardSphere

end

end OAI
