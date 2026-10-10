import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedWindowFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveRadialMellin

namespace OAI

/-! Entire radial factors for the actual shifted frequency, including a
finite closed height window. The endpoint changes are null sets. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedPositiveRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (ε : ℝ) (s : ℂ) : ℂ :=
  ∫ v in Ioi ε,star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3

lemma cubicThetaShiftedRadial_height_dilation (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {v : ℝ} (hv : 0<v) (s : ℂ) :
    star (W v)*(v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3=
    ∫ u in Ioi (0:ℝ),cubicThetaRadialMellinIntegrand W
      (cubicThetaShiftedRowHeatScale h) s (v,u) := by
  rw [show star (W v)*(v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3=
      star (W v)/(v:ℂ)^3*((v:ℂ)^s*
        (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)) by ring,
    cubicThetaHeat_height_dilation hv]
  calc
    _ = star (W v)/(v:ℂ)^2*
        ∫ u in Ioi (0:ℝ),(u:ℂ)^(s-2)*
          cubicThetaLinearHeat v (cubicThetaShiftedRowHeatScale h) u := by
      field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
    _ = _ := by
      rw [←integral_const_mul]
      congr 1
      ext u
      unfold cubicThetaRadialMellinIntegrand
      ring

lemma cubicThetaShiftedPositiveRadial_integrable {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    IntegrableOn (fun v => star (W v)*(v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3)
      (Ioi ε) := by
  have hi := (cubicThetaPositiveRadialMellin_integrable W hε
    (cubicThetaShiftedRowHeatScale_pos hh) s).integral_prod_left
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (cubicThetaShiftedRadial_height_dilation h W (hε.trans hv) s).symm

lemma cubicThetaShiftedPositiveRadial_mellin {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    cubicThetaShiftedPositiveRadialTest h W ε s=
      mellin (cubicThetaPositiveAveragedHeat W ε (cubicThetaShiftedRowHeatScale h)) (s-1) := by
  unfold cubicThetaShiftedPositiveRadialTest
  calc
    _ = ∫ v in Ioi ε,∫ u in Ioi (0:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaShiftedRowHeatScale h) s (v,u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact cubicThetaShiftedRadial_height_dilation h W (hε.trans hv) s
    _ = ∫ u in Ioi (0:ℝ),∫ v in Ioi ε,
        cubicThetaRadialMellinIntegrand W (cubicThetaShiftedRowHeatScale h) s (v,u) :=
      integral_integral_swap (cubicThetaPositiveRadialMellin_integrable W hε
        (cubicThetaShiftedRowHeatScale_pos hh) s)
    _ = _ := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards with u
      simp only [show s-1-1=s-2 by ring,smul_eq_mul,cubicThetaPositiveAveragedHeat]
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      unfold cubicThetaRadialMellinIntegrand
      ring

lemma cubicThetaShiftedPositiveRadial_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) :
    Differentiable ℂ (cubicThetaShiftedPositiveRadialTest h W ε) := by
  rw [show cubicThetaShiftedPositiveRadialTest h W ε=
    (fun s : ℂ => mellin (cubicThetaPositiveAveragedHeat W ε
      (cubicThetaShiftedRowHeatScale h)) (s-1)) from
        funext (cubicThetaShiftedPositiveRadial_mellin hh W hε)]
  exact (cubicThetaPositiveAveragedHeat_mellin_entire W hε
    (cubicThetaShiftedRowHeatScale_pos hh)).comp (differentiable_id.sub_const 1)

lemma cubicThetaShiftedWindowRadial_sub {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) (s : ℂ) :
    cubicThetaShiftedWindowRadialTest h W a d s=
      cubicThetaShiftedPositiveRadialTest h W a s-cubicThetaShiftedPositiveRadialTest h W d s := by
  unfold cubicThetaShiftedWindowRadialTest cubicThetaShiftedPositiveRadialTest
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le had,
    intervalIntegral.integral_Ioi_sub_Ioi
      (cubicThetaShiftedPositiveRadial_integrable hh W ha s) had]

lemma cubicThetaShiftedWindowRadial_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) :
    Differentiable ℂ (cubicThetaShiftedWindowRadialTest h W a d) := by
  rw [show cubicThetaShiftedWindowRadialTest h W a d=
    (fun s => cubicThetaShiftedPositiveRadialTest h W a s-
      cubicThetaShiftedPositiveRadialTest h W d s) from
        funext (cubicThetaShiftedWindowRadial_sub hh W ha had)]
  exact (cubicThetaShiftedPositiveRadial_entire hh W ha).sub
    (cubicThetaShiftedPositiveRadial_entire hh W (ha.trans_le had))

end CubicFirstMoment

end

end OAI
