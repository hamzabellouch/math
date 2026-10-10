import OAI.Analysis.LienardCycles.CurvaturePositive

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
namespace QuinticLienard.QuinticFit
open ScalarArcs PartialCalculus QuadraticCoordinates
lemma profile_neg (a : Fin 6 → ℝ) (q : ℝ × ℝ) :
    QuinticProfile.profile (-a) q = -QuinticProfile.profile a q := by
  dsimp [QuinticProfile.profile,ScaledProfile.poly]
  ring
lemma M_neg (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : M (-a) (h,r) = -M a (h,r) := by
  let Φ := QuinticProfile.profile a
  let t := PositiveWidth.peakAtWidth Φ ((0,h),r)
  have hs := PositiveWidth.peak_spec Φ (fun _ ht=>QuinticProfile.analytic a ht)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have ha := chosen_arch (positive_arch_exists (PositiveWidth.profile_C1 Φ
    (fun _ ht=>QuinticProfile.analytic a ht) 0) hh hs.1)
  have hb := ArchSymmetries.IsArch.reflect ha
  have hf : (fun x=> -Φ (0,x)) = (fun x=>QuinticProfile.profile (-a) (0,x)) := by
    funext x
    exact (profile_neg a (0,x)).symm
  rw [hf] at hb
  have hw : (-lower (fun x=>Φ (0,x)) h t- -upper (fun x=>Φ (0,x)) h t)/2=r := by
    have hs2 := hs.2
    change (upper (fun x=>Φ (0,x)) h t-lower (fun x=>Φ (0,x)) h t)/2=r at hs2
    linarith [hs2]
  have hm := PositiveWidth.midpoint_of_arch (QuinticProfile.profile (-a))
    (fun _ ht=>QuinticProfile.analytic (-a) ht) (QuinticProfile.local_flow (-a)) hb hh hs.1 hr hw
  change M (-a) (h,r)=_ at hm
  rw [hm,profile_neg]
  dsimp [M,PositiveTransport.M,PositiveWidth.midpointAtWidth,PositiveWidth.midpointFamily,ScalarArcs.midpoint,t,Φ]
  ring
lemma V_neg (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : V (-a) (h,r) = -V a (h,r) := by
  apply (second_hasDerivAt ((M_analytic (-a) hh hr).differentiableAt (by simp))).unique
  apply (second_hasDerivAt ((M_analytic a hh hr).differentiableAt (by simp))).neg.congr_of_eventuallyEq
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  exact M_neg a hh hs
lemma Hr_neg (d k : ℝ) {r : ℝ} (hr : 0<r) : Hr ((-d,-k),r) = -Hr ((d,k),r) := by
  apply (Hr_hasDerivAt (d:= -d) (k:= -k) hr).unique
  apply (Hr_hasDerivAt (d:=d) (k:=k) hr).neg.congr_of_eventuallyEq
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  exact reflection d k hs
lemma fit_neg (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    lambda (-a) (h,r) = -lambda a (h,r) ∧ kappa (-a) (h,r) = -kappa a (h,r) := by
  have hm : H ((-lambda a (h,r),-kappa a (h,r)),r)=M (-a) (h,r) := by
    rw [reflection _ _ hr,M_neg a hh hr]
    exact congrArg Neg.neg (spec a hh hr).1
  have hv : Hr ((-lambda a (h,r),-kappa a (h,r)),r)=V (-a) (h,r) := by
    rw [Hr_neg _ _ hr,V_neg a hh hr]
    exact congrArg Neg.neg (spec a hh hr).2
  have hf := QuadraticFit.fit_unique hr (M_abs_lt (-a) hh hr) (V_abs_lt (-a) hh hr) hm hv
  rw [(fit_eq (-a) hh hr).1,(fit_eq (-a) hh hr).2]
  exact hf
lemma w_neg (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : w (-a) (h,r) = -w a (h,r) := by
  apply (second_hasDerivAt ((kappa_analytic (-a) hh hr).differentiableAt (by simp))).unique
  apply (second_hasDerivAt ((kappa_analytic a hh hr).differentiableAt (by simp))).neg.congr_of_eventuallyEq
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  exact (fit_neg a hh hs).2
end QuinticLienard.QuinticFit
namespace QuinticLienard.ScaledProfile
lemma slope_neg (a : Fin 6 → ℝ) (h : ℝ) : slope (-a) h = -slope a h := by
  dsimp [slope,c₁]
  ring
lemma curvature_neg (a : Fin 6 → ℝ) (h : ℝ) : curvature (-a) h = -curvature a h := by
  dsimp [curvature,c₁,c₂]
  ring
lemma third_neg (a : Fin 6 → ℝ) (h : ℝ) : third (-a) h = -third a h := by
  dsimp [third,rem,c₁,c₂,c₃,c₄]
  ring
end QuinticLienard.ScaledProfile
namespace QuinticLienard.QuinticFit
lemma lambda_gt_slope {a : Fin 6 → ℝ} {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (hthird : ∀ u, 0<u → ScaledProfile.third a u<0) : ScaledProfile.slope a h<lambda a (h,r) := by
  have hp : ∀ u, 0<u → 0<ScaledProfile.third (-a) u := by
    intro u hu
    rw [ScaledProfile.third_neg]
    exact neg_pos.mpr (hthird u hu)
  have hl := lambda_lt_slope hh hr hp
  rw [(fit_neg a hh hr).1,ScaledProfile.slope_neg] at hl
  linarith
lemma kappa_width_neg {a : Fin 6 → ℝ} {h r : ℝ} (hh : 0<h) (hr : 0<r)
    (hthird : ∀ u, 0<u → ScaledProfile.third a u<0) : w a (h,r)<0 := by
  have hp : ∀ u, 0<u → 0<ScaledProfile.third (-a) u := by
    intro u hu
    rw [ScaledProfile.third_neg]
    exact neg_pos.mpr (hthird u hu)
  have hl := kappa_width_pos hh hr hp
  rw [w_neg a hh hr] at hl
  linarith
end QuinticLienard.QuinticFit

end OAI
