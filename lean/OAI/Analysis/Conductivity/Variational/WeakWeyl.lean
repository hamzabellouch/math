import Mathlib
import OAI.Analysis.Conductivity.Variational.L2TranslationAverage

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma closedBall_near_subset {a x : WeylSpace} {R : ℝ} (hR : 0<R)
    (hx : x∈Metric.ball a (R/4)) : Metric.closedBall x (R/2)⊆Metric.closedBall a R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  have hxa : dist x a<R/4 := hx
  exact (dist_triangle y x a).trans (by linarith)

theorem weakWeyl_local {f : WholeL2} {U : Set WeylSpace}
    (hw : WeaklyHarmonicOn f U) {a : WeylSpace} {R : ℝ} (hR : 0<R)
    (hball : Metric.closedBall a R⊆U) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (radialMollify f (R/4)) ∧
    (f : WeylSpace → ℝ) =ᵐ[volume.restrict (Metric.ball a (R/4))] radialMollify f (R/4) := by
  have hf : LocallyIntegrable (f : WeylSpace → ℝ) := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hs : 0<R/4 := by linarith
  refine ⟨radialMollify_smooth hf hs,?_⟩
  let V := Metric.ball a (R/4)
  let g := radialMollify f (R/4)
  have he (r : ℝ) (hr : 0<r ∧ r<R/2) (x : WeylSpace) (hx : x∈V) :
      g x=radialMollify f r x :=
    radialMollify_scale_independent hf hw ((closedBall_near_subset hR hx).trans hball)
      ⟨hs,by linarith⟩ hr
  have hi : Integrable (fun x => (g x-f x)^2) :=
    ((radialMollify_memLp hs f).sub (Lp.memLp f)).integrable_sq
  have hbound (ε : ℝ) (hε : 0<ε) : (∫ x in V, (g x-f x)^2)≤ε := by
    obtain ⟨δ,hδ,hd⟩ := radialMollify_approx f hε
    let r := min δ (R/4)/2
    have hr : 0<r := by dsimp [r]; positivity
    have hrδ : r≤δ := by dsimp [r]; have := min_le_left δ (R/4); linarith [lt_min hδ hs]
    have hrR : r<R/2 := by dsimp [r]; have := min_le_right δ (R/4); linarith
    have heq : (∫ x in V, (g x-f x)^2)=∫ x in V, (radialMollify f r x-f x)^2 := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      change (g x-f x)^2=(radialMollify f r x-f x)^2
      rw [he r ⟨hr,hrR⟩ x hx]
    rw [heq]
    exact (setIntegral_le_integral ((radialMollify_memLp hr f).sub (Lp.memLp f)).integrable_sq
      (ae_of_all _ (fun x => sq_nonneg _))).trans (hd r hr hrδ)
  have hz : (∫ x in V, (g x-f x)^2)=0 := by
    apply le_antisymm _ (integral_nonneg (fun x => sq_nonneg _))
    by_contra hn
    have hp : 0<(∫ x in V, (g x-f x)^2) := lt_of_not_ge hn
    have hh := hbound ((∫ x in V, (g x-f x)^2)/2) (by linarith)
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg (g x-f x)))
    hi.restrict).mp hz
  filter_upwards [hae] with x hx
  exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hx)).symm

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Convolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def radialAverageF (f : WeylSpace → F) (s : ℝ) : WeylSpace → F :=
  radialEta radialProfile s ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f

def RadialMeanOn (f : WeylSpace → F) (a : WeylSpace) (R : ℝ) : Prop :=
  ∀ s : ℝ, 0<s → ∀ x : WeylSpace, dist x a+s<R → f x=radialAverageF f s x

omit [CompleteSpace F]

lemma radialAverageF_fderiv {f : WeylSpace → F} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) {s : ℝ} (_ : 0<s) (x : WeylSpace) :
    fderiv ℝ (radialAverageF f s) x=radialAverageF (fderiv ℝ f) s x := by
  have hd := hc.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    (radialEta_smooth s).continuous.locallyIntegrable (hf.of_le (by simp)) x
  unfold radialAverageF
  rw [hd.fderiv]
  congr 1

lemma RadialMeanOn.derivative {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) : RadialMeanOn (fderiv ℝ f) a R := by
  intro s hs x hx
  have he : f =ᶠ[𝓝 x] radialAverageF f s := by
    have ho : IsOpen {y : WeylSpace | dist y a+s<R} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [ho.mem_nhds hx] with y hy
    exact hm s hs y hy
  rw [he.fderiv_eq,radialAverageF_fderiv hf hc hs]

lemma RadialMeanOn.derivative_bound {f : WeylSpace → F} {a x : WeylSpace} {R s M : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : 0<s) (hx : dist x a+s<R) (_ : 0≤M)
    (hb : ∀ y∈Metric.closedBall x s, ‖f y‖≤M) :
    ‖fderiv ℝ f x‖≤M*(∫ y, ‖fderiv ℝ (radialEta radialProfile s) y‖) := by
  have he : f =ᶠ[𝓝 x] radialAverageF f s := by
    have ho : IsOpen {y : WeylSpace | dist y a+s<R} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [ho.mem_nhds hx] with y hy
    exact hm s hs y hy
  have hd := (radialEta_compact hs).hasFDerivAt_convolution_left (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) ((radialEta_smooth s).of_le (by simp))
    hf.continuous.locallyIntegrable x
  rw [he.fderiv_eq]
  unfold radialAverageF
  rw [hd.fderiv]
  let L : (WeylSpace →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] (WeylSpace →L[ℝ] F) := (ContinuousLinearMap.lsmul ℝ ℝ).precompL WeylSpace
  have hi := ((radialEta_compact hs).fderiv ℝ).convolutionExists_left (μ := volume) L
    ((radialEta_smooth s).continuous_fderiv (by simp)) hf.continuous.locallyIntegrable x
  have hn : Integrable (fun y => M*‖fderiv ℝ (radialEta radialProfile s) y‖) :=
    (((radialEta_smooth s).continuous_fderiv (by simp)).integrable_of_hasCompactSupport
      ((radialEta_compact hs).fderiv ℝ)).norm.const_mul M
  calc
    _ ≤ ∫ y, ‖L (fderiv ℝ (radialEta radialProfile s) y) (f (x-y))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, M*‖fderiv ℝ (radialEta radialProfile s) y‖ := by
      apply integral_mono_ae hi.norm hn
      filter_upwards with y
      by_cases hy : ‖y‖ ≤ s
      · have hb' : ‖f (x-y)‖≤M := hb _ (by simpa [Metric.mem_closedBall,dist_eq_norm] using hy)
        change ‖(fderiv ℝ (radialEta radialProfile s) y).smulRight (f (x-y))‖ ≤ _
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact (mul_le_mul_of_nonneg_left hb' (norm_nonneg _)).trans_eq (mul_comm _ _)
      · have hz : fderiv ℝ (radialEta radialProfile s) y=0 := by
          apply Function.notMem_support.mp
          intro hd
          have ht := support_fderiv_subset ℝ hd
          revert ht
          intro ht
          have hsub : tsupport (radialEta radialProfile s)⊆Metric.closedBall (0:WeylSpace) s := by
            apply closure_minimal _ Metric.isClosed_closedBall
            intro z hz
            rw [Metric.mem_closedBall,dist_zero_right]
            exact le_of_not_gt (fun hh => hz (radialEta_zero hs hh.le))
          exact hy (by simpa [Metric.mem_closedBall,dist_zero_right] using hsub ht)
        simp [hz,L]
    _ = M*(∫ y, ‖fderiv ℝ (radialEta radialProfile s) y‖) := integral_const_mul _ _

end ScalarConductivity

end

end OAI
