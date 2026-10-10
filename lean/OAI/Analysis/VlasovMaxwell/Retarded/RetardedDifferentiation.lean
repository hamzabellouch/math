import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma norm_velocity_integral_bound {P C : ℝ} {g : Vec → ℝ}
    (hzero : ∀ v, P<‖v‖ → g v=0) (hb : ∀ v, ‖v‖≤P → |g v|≤C) :
    ‖∫ v,g v‖≤volume.real (closedBall (0:Vec) P)*C := by
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall (0:Vec) P)
    (f:=g) (fun v hv => hzero v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv))]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P)) (f:=g) (C:=C) (by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
    simpa only [Real.norm_eq_abs] using hb v (by simpa only [mem_closedBall,dist_zero_right] using hv))
  simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh

lemma retarded_packet_integrable {F : Vec × Phase → ℝ} {t P C : ℝ} (x : Vec)
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖) :
    IntegrableOn (fun z => ∫ v,F (x,z,v)) (ball (0:Vec) t) := by
  let A := ball (0:Vec) t \ ({0}:Set Vec)
  have hC : ContinuousOn (fun p : Phase => F (x,p)) (A ×ˢ univ) := by
    intro p hp
    exact ((hc (x,p) hp.1.2 (by simpa only [mem_ball,dist_zero_right] using hp.1.1)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hzero (z : Vec) (hza : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (x,z,v)=0 :=
    hz x z v hza.2 (by simpa only [mem_ball,dist_zero_right] using hza.1)
      (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=volume.real (closedBall (0:Vec) P)*C)
    (by norm_num) (continuousOn_integral_uniform_support (isCompact_closedBall _ _) hC hzero)
  intro z hz0 hzt
  have hzn := norm_pos_iff.mp hz0
  have hh := norm_velocity_integral_bound (hz x z · hzn hzt) (hb x z · hzn hzt)
  simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh

lemma retarded_packet_spatial_fderiv {F : Vec × Phase → ℝ} {x z v : Vec}
    (hF : DifferentiableAt ℝ F (x,z,v)) (e : Vec) :
    fderiv ℝ (fun y => F (y,z,v)) x e=fderiv ℝ F (x,z,v) (e,0,0) := by
  have hh := hF.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma retarded_packet_derivative_zero {F : Vec × Phase → ℝ} {P t : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z v e : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) (hv : P<‖v‖) :
    fderiv ℝ F (x,z,v) (e,0,0)=0 := by
  rw [←retarded_packet_spatial_fderiv ((hF (x,z,v) hz0 hzt).differentiableAt (by simp)) e]
  have he : (fun y => F (y,z,v))=fun _ => (0:ℝ) := funext (fun y => hz y z v hz0 hzt hv)
  rw [he]
  simp

lemma hasDerivAt_retarded_packet_line {F : Vec × Phase → ℝ} {t P : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z e : Vec) (a : ℝ) (hz0 : z≠0) (hzt : ‖z‖<t) :
    HasDerivAt (fun q : ℝ => ∫ v,F (x+q • e,z,v))
      (∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let G : ℝ × Vec → ℝ := fun p => F (x+p.1 • e,z,p.2)
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (hF (x+p.1 • e,z,p.2) hz0 hzt).comp p
      ((contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk
        (contDiffAt_const.prodMk contDiffAt_snd))
  have hzero (q : ℝ) (_ : q∈(univ : Set ℝ)) (v : Vec) (hv : v∉closedBall (0:Vec) P) : G (q,v)=0 :=
    hz _ z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  have hd := (hasFDerivAt_integral_uniform_support isOpen_univ (isCompact_closedBall (0:Vec) P)
    (mem_univ a) hG.contDiffOn hzero).differentiableAt.hasDerivAt
  rw [show deriv (fun q => ∫ v,G (q,v)) a = fderiv ℝ (fun q => ∫ v,G (q,v)) a 1 from rfl,
    fderiv_integral_uniform_support_apply isOpen_univ (isCompact_closedBall (0:Vec) P)
      (mem_univ a) hG.contDiffOn hzero] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  apply ae_of_all
  intro v
  have hm := ((hasFDerivAt_const x (a,v)).add ((hasFDerivAt_fst (𝕜:=ℝ)).smul_const e)).prodMk
    ((hasFDerivAt_const z (a,v)).prodMk (hasFDerivAt_snd (𝕜:=ℝ)))
  have hh := ((hF (x+a • e,z,v) hz0 hzt).differentiableAt (by simp)).hasFDerivAt.comp (a,v) hm
  change HasFDerivAt G _ (a,v) at hh
  simpa using congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L (1,0)) hh.fderiv

lemma hasDerivAt_retarded_packet_integral {F : Vec × Phase → ℝ} {t P C D : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖)
    (x e : Vec) (a : ℝ)
    (hD : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |fderiv ℝ F (x,z,v) (e,0,0)|≤D/‖z‖) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,F (x+q • e,z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let V := volume.real (closedBall (0:Vec) P)
  have hfc := fun p hp ht => (hF p hp ht).continuousAt
  have hdc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t →
      ContinuousAt (fun p => fderiv ℝ F p (e,0,0)) p := by
    intro p hp ht
    exact ((hF p hp ht).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hdz := fun x z v hz0 hzt hv => retarded_packet_derivative_zero hF hz x z v e hz0 hzt hv
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:=fun z : Vec => V*D*‖z‖^(-(1:ℝ))) (by simp)
    (Eventually.of_forall (fun q => (retarded_packet_integrable (x+q • e) hfc hz hb).aestronglyMeasurable))
    (retarded_packet_integrable (x+a • e) hfc hz hb)
    (retarded_packet_integrable (x+a • e) hdc hdz hD).aestronglyMeasurable
    ?_ ((integrableOn_norm_rpow_neg (R:=t) (show (1:ℝ)<3 by norm_num)).const_mul (V*D)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hzball
    have hh := norm_velocity_integral_bound (hdz (x+q • e) z · hz0 hzt) (hD (x+q • e) z · hz0 hzt)
    simpa only [V,Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    exact hasDerivAt_retarded_packet_line hF hz x z e q hz0 (by simpa only [mem_ball,dist_zero_right] using hzball)

end RVM
end

end OAI
