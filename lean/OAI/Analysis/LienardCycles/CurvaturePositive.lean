import OAI.Analysis.LienardCycles.ActualSlopeComparison

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
noncomputable def w (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := QuinticFit.w a (point a t s)
noncomputable def damp (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := g a t s/s*QuinticFit.T a (point a t s)
noncomputable def feed (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := g a t s/s*Cr (QuinticFit.fit a (point a t s))*(QuinticFit.lambda a (point a t s)-k a t s)
lemma w_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (w a t) r :=
  (QuinticFit.w_analytic a (base_spec he).1 (radius_pos he)).comp (f:=point a t) r (point_analytic he)
lemma damp_continuous {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContinuousAt (damp a t) r := by
  have hT : ContinuousAt (fun s=>QuinticFit.T a (point a t s)) r :=
    (QuinticFit.T_analytic a (base_spec he).1 (radius_pos he)).continuousAt.comp (f:=point a t) (point_analytic he).continuousAt
  exact (((continuousAt_id.pow 2).sub ((m_analytic he).continuousAt.pow 2)).div continuousAt_id (radius_pos he).ne').mul hT
lemma w_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (w a t) (-damp a t r*w a t r+feed a t r) r := by
  have hd := along_deriv he ((QuinticFit.w_analytic a (base_spec he).1 (radius_pos he)).differentiableAt (by simp))
  dsimp only [point] at hd
  rw [QuinticFit.w_transport a (base_spec he).1 (radius_pos he)] at hd
  convert! hd using 1
  dsimp only [damp,w,feed,k,point]
  ring
lemma feed_nonneg {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) : 0≤feed a t r := by
  dsimp only [feed]
  exact mul_nonneg_of_nonpos_of_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (div_pos (g_pos he) (radius_pos he)).le (Cr_nonpos (radius_pos he)))
    (sub_nonpos.mpr (fitted_slope_lt he hthird).le)
lemma w_small {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0<w a t s := by
  have ht := (base_spec he).1.trans (base_spec he).2.1
  have hl := QuinticFit.kappa_deriv_limit (a:=a) ht (base_tendsto he)
    (tendsto_id.mono_left inf_le_left) self_mem_nhdsWithin
  have hp : 0<4*ScaledProfile.third a t/7 := by
    have := hthird t ht
    positivity
  filter_upwards [hl.eventually (eventually_gt_nhds hp),self_mem_nhdsWithin,
    (eventually_lt_nhds (radius_pos he)).filter_mono inf_le_left] with s hs hs0 hsr
  have he' := adm_le he hs0 hsr.le
  have hd := second_hasDerivAt ((QuinticFit.kappa_analytic a (base_spec he').1 hs0).differentiableAt (by simp))
  simp only [id_eq] at hs
  rw [hd.deriv] at hs
  exact (div_pos_iff_of_pos_right hs0).mp hs

theorem w_pos {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) : 0<w a t r := by
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s ∧ s<r ∧ 0<w a t s := by
    filter_upwards [w_small he hthird,self_mem_nhdsWithin,
      (eventually_lt_nhds (radius_pos he)).filter_mono inf_le_left] with s hw hs hsr
    exact ⟨hs,hsr,hw⟩
  obtain ⟨s,hs,hsr,hws⟩ := hev.exists
  apply ScalarComparison.linear_pos_of_nonneg (a:=damp a t) (F:=feed a t) hsr.le
    (fun u hu => (damp_continuous (adm_le he (hs.trans_le hu.1) hu.2)).continuousWithinAt)
    (fun u hu => w_deriv (adm_le he (hs.trans_le hu.1) hu.2))
    (fun u hu => feed_nonneg (adm_le he (hs.trans hu.1) hu.2.le) hthird) hws
end QuinticLienard.ActualCharacteristic
namespace QuinticLienard.QuinticFit

theorem kappa_width_pos {a : Fin 6 → ℝ} {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (hthird : ∀ u, 0<u → 0<ScaledProfile.third a u) : 0<w a (h,r) := by
  let t := PositiveWidth.peakAtWidth (QuinticProfile.profile a) ((0,h),r)
  have ht := PositiveWidth.peak_spec (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have he : ActualCharacteristic.Adm a t r := ⟨h,hh,ht.1,ht.2⟩
  have hb : ActualCharacteristic.b a t r=h := PositiveWidth.base_eq _
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh ht.1 ht.2
  simpa only [ActualCharacteristic.w,ActualCharacteristic.point,hb] using
    ActualCharacteristic.w_pos he hthird
end QuinticLienard.QuinticFit

end OAI
