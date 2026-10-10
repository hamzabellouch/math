import OAI.Analysis.LienardCycles.ProfileComparison

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
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus
noncomputable def C (q : (ℝ × ℝ) × ℝ) : ℝ := R q/G q
noncomputable def Cr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) C
noncomputable def Cd : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) C
noncomputable def Ck : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) C
lemma G_analytic {d k r : ℝ} (hr : 0<r) : ContDiffAt ℝ ω G ((d,k),r) :=
  ((P_analytic hr).mul (S_analytic hr)).sub ((Q_analytic hr).mul (R_analytic hr))
lemma C_analytic {d k r : ℝ} (hr : 0<r) : ContDiffAt ℝ ω C ((d,k),r) :=
  (R_analytic hr).div (G_analytic hr) (G_pos hr).ne'
lemma Cr_analytic {d k r : ℝ} (hr : 0<r) : ContDiffAt ℝ ω Cr ((d,k),r) := direction_contDiffAt (C_analytic hr) _
lemma Cd_analytic {d k r : ℝ} (hr : 0<r) : ContDiffAt ℝ ω Cd ((d,k),r) := direction_contDiffAt (C_analytic hr) _
lemma Ck_analytic {d k r : ℝ} (hr : 0<r) : ContDiffAt ℝ ω Ck ((d,k),r) := direction_contDiffAt (C_analytic hr) _
lemma Cr_nonpos {d k r : ℝ} (hr : 0<r) : Cr ((d,k),r)≤0 := by
  have hd := slice_r ((C_analytic (d:=d) (k:=k) hr).differentiableAt (by simp))
  change direction ((0,0),1) C ((d,k),r)≤0
  rw [←hd.deriv]
  exact model_inequality hr
end QuinticLienard.QuadraticCoordinates

namespace QuinticLienard.QuinticFit
open PartialCalculus QuadraticCoordinates
noncomputable def w (a : Fin 6 → ℝ) : ℝ × ℝ → ℝ := second (kappa a)
noncomputable def T (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ :=
  second (α a) q+C (fit a q)*Q (fit a q)/P (fit a q)-
    (Ck (fit a q)-Q (fit a q)/P (fit a q)*Cd (fit a q))*(lambda a q-ScaledProfile.slope a q.1)
lemma gap_pos (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : 0<r^2-(M a (h,r))^2 :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos hr] using M_abs_lt a hh hr))
lemma α_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (α a) (h,r) :=
  contDiffAt_snd.div ((contDiffAt_snd.pow 2).sub ((M_analytic a hh hr).pow 2)) (gap_pos a hh hr).ne'
lemma fit_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (fit a) (h,r) :=
  ((lambda_analytic a hh hr).prodMk (kappa_analytic a hh hr)).prodMk contDiffAt_snd
lemma w_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (w a) (h,r) :=
  second_contDiffAt (kappa_analytic a hh hr)
lemma T_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (T a) (h,r) := by
  have hf := fit_analytic a hh hr
  have hP : ContDiffAt ℝ ω (fun q=>P (fit a q)) (h,r) := (P_analytic hr).comp (f:=fit a) (h,r) hf
  have hQ : ContDiffAt ℝ ω (fun q=>Q (fit a q)) (h,r) := (Q_analytic hr).comp (f:=fit a) (h,r) hf
  have hC : ContDiffAt ℝ ω (fun q=>C (fit a q)) (h,r) := (C_analytic hr).comp (f:=fit a) (h,r) hf
  have hd : ContDiffAt ℝ ω (fun q=>Cd (fit a q)) (h,r) := (Cd_analytic hr).comp (f:=fit a) (h,r) hf
  have hk : ContDiffAt ℝ ω (fun q=>Ck (fit a q)) (h,r) := (Ck_analytic hr).comp (f:=fit a) (h,r) hf
  exact ((second_contDiffAt (α_analytic a hh hr)).add ((hC.mul hQ).div hP (QuadraticVariation.P_pos hr).ne')).sub
    ((hk.sub ((hQ.div hP (QuadraticVariation.P_pos hr).ne').mul hd)).mul
      ((lambda_analytic a hh hr).sub ((ScaledProfile.slope_analytic a hh).comp (h,r) contDiffAt_fst)))

theorem w_transport (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    D a (w a) (h,r)=T a (h,r)*w a (h,r)-Cr (fit a (h,r))*(lambda a (h,r)-ScaledProfile.slope a h) := by
  have hK := kappa_analytic a hh hr
  have hL := lambda_analytic a hh hr
  have hα := α_analytic a hh hr
  have hC := (C_analytic (d:=lambda a (h,r)) (k:=kappa a (h,r)) hr).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f:=fun s=>fit a (h,s)) r
      (((second_hasDerivAt (hL.differentiableAt (by simp))).prodMk
        (second_hasDerivAt (hK.differentiableAt (by simp)))).prodMk (hasDerivAt_id r))
  rw [fderiv_model] at hC
  have hd := ((second_hasDerivAt ((first_contDiffAt hK).differentiableAt (by simp))).sub
    ((second_hasDerivAt (hα.differentiableAt (by simp))).mul
      (second_hasDerivAt ((second_contDiffAt hK).differentiableAt (by simp)))))
  have hc := hC.neg.mul ((second_hasDerivAt (hL.differentiableAt (by simp))).sub_const (ScaledProfile.slope a h))
  have he : (fun s=>first (kappa a) (h,s)-α a (h,s)*second (kappa a) (h,s)) =ᶠ[𝓝 r]
      (fun s=>-C (fit a (h,s))*(lambda a (h,s)-ScaledProfile.slope a h)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    simpa only [D,C,neg_div] using (fit_transport a hh hs).2.1
  have hq := hd.unique (hc.congr_of_eventuallyEq he)
  rw [←mixed_comm hK] at hq
  have hp := (fit_transport a hh hr).1
  have hPe : P (fit a (h,r))≠0 := (QuadraticVariation.P_pos (d:=lambda a (h,r)) (k:=kappa a (h,r)) hr).ne'
  change _ = -(second (lambda a) (h,r)*Cd (fit a (h,r))+second (kappa a) (h,r)*Ck (fit a (h,r))+1*Cr (fit a (h,r)))*
    (lambda a (h,r)-ScaledProfile.slope a h)+-C (fit a (h,r))*second (lambda a) (h,r) at hq
  have hlam : second (lambda a) (h,r)= -Q (fit a (h,r))/P (fit a (h,r))*w a (h,r) := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hPe).mpr
    dsimp only [w]
    nlinarith only [hp]
  rw [hlam] at hq
  dsimp only [D,T,w] at hq ⊢
  field_simp [hPe] at hq ⊢
  linear_combination hq
end QuinticLienard.QuinticFit

end OAI
