import OAI.Analysis.LienardCycles.FixedSlopeLimit

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
noncomputable def j (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := QuadraticFit.slope ((κ,s),m a t s)
noncomputable def err (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := k a t s-j a t κ s
noncomputable def coeff (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := g a t s/(s*P ((j a t κ s,κ),s))
noncomputable def label (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := QuadraticFit.label ((κ,s),A a t s)
lemma j_analytic {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (j a t κ) r :=
  (QuadraticFit.slope_analytic (k:=κ) (radius_pos he) (m_abs_lt he)).comp
    (f:=fun s=>((κ,s),m a t s)) r ((contDiffAt_const.prodMk contDiffAt_id).prodMk (m_analytic he))
lemma j_spec {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : H ((j a t κ r,κ),r)=m a t r :=
  QuadraticFit.slope_spec (radius_pos he) (m_abs_lt he)
lemma j_deriv {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    HasDerivAt (j a t κ) (-κ*g a t r/r+coeff a t κ r*err a t κ r) r := by
  have hj := (j_analytic (κ:=κ) he).differentiableAt (by simp)
  have hd := (H_analytic (d:=j a t κ r) (k:=κ) (radius_pos he)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f:=fun s=>((j a t κ s,κ),s)) r
      ((hj.hasDerivAt.prodMk (hasDerivAt_const r κ)).prodMk (hasDerivAt_id r))
  have hev : (fun s=>H ((j a t κ s,κ),s)) =ᶠ[𝓝 r] m a t := by
    filter_upwards [adm_eventually he] with s hs
    exact j_spec hs
  have hq := hd.unique ((m_deriv he).congr_of_eventuallyEq hev)
  rw [fderiv_model] at hq
  change deriv (j a t κ) r*P ((j a t κ r,κ),r)+0*Q ((j a t κ r,κ),r)+1*Hr ((j a t κ r,κ),r)=_ at hq
  have hw := width_identity (d:=j a t κ r) (k:=κ) (radius_pos he)
  change κ*P ((j a t κ r,κ),r)+j a t κ r=(r*Hr ((j a t κ r,κ),r)+H ((j a t κ r,κ),r))/(r^2-H ((j a t κ r,κ),r)^2) at hw
  rw [j_spec he] at hw
  have hP := (QuadraticVariation.P_pos (d:=j a t κ r) (k:=κ) (radius_pos he)).ne'
  have heq : deriv (j a t κ) r = -κ*g a t r/r+coeff a t κ r*err a t κ r := by
    dsimp only [coeff,err]
    change κ*P ((j a t κ r,κ),r)+j a t κ r=(r*Hr ((j a t κ r,κ),r)+m a t r)/g a t r at hw
    have hw' := (eq_div_iff (g_pos he).ne').mp hw
    have hq' : (deriv (j a t κ) r*P ((j a t κ r,κ),r)+Hr ((j a t κ r,κ),r))*r = -m a t r+g a t r*k a t r := by
      calc
        _ = (-m a t r/r+g a t r/r*k a t r)*r := by
          congr 1
          simpa only [zero_mul,one_mul,add_zero] using hq
        _ = _ := by field_simp [(radius_pos he).ne']
    field_simp [(radius_pos he).ne',hP]
    nlinarith [hw',hq']
  rw [←heq]
  exact hj.hasDerivAt
lemma err_deriv {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    HasDerivAt (err a t κ) (-coeff a t κ r*err a t κ r-g a t r/r*(c a t r-κ)) r := by
  convert! (k_deriv he).sub (j_deriv (κ:=κ) he) using 1
  ring
lemma coeff_pos {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : 0<coeff a t κ r :=
  div_pos (g_pos he) (mul_pos (radius_pos he) (QuadraticVariation.P_pos (radius_pos he)))
lemma coeff_continuous {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : ContinuousAt (coeff a t κ) r := by
  have hq : ContinuousAt (fun s=>((j a t κ s,κ),s)) r :=
    (((j_analytic he).continuousAt.prodMk continuousAt_const).prodMk continuousAt_id)
  have hP : ContinuousAt (fun s=>P ((j a t κ s,κ),s)) r :=
    (P_analytic (d:=j a t κ r) (k:=κ) (radius_pos he)).continuousAt.comp (f:=fun s=>((j a t κ s,κ),s)) hq
  exact ((continuousAt_id.pow 2).sub ((m_analytic he).continuousAt.pow 2)).div
    (continuousAt_id.mul hP) (mul_ne_zero (radius_pos he).ne' (QuadraticVariation.P_pos (radius_pos he)).ne')
lemma err_tendsto {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) (κ : ℝ) :
    Tendsto (err a t κ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hj := QuinticFit.fixed_slope_limit (a:=a) ((base_spec he).1.trans (base_spec he).2.1) κ
    (base_tendsto he) (tendsto_id.mono_left inf_le_left) self_mem_nhdsWithin
  change Tendsto (fun s=>k a t s-QuadraticFit.slope ((κ,s),QuinticFit.M a (b a t s,s))) (𝓝[>] (0:ℝ)) (𝓝 0)
  simpa only [sub_self,id_eq] using (small_limits he).2.2.1.sub hj
lemma label_analytic {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (label a t κ) r :=
  (QuadraticFit.label_analytic (k:=κ) (radius_pos he) (A_abs_lt he)).comp
    (f:=fun s=>((κ,s),A a t s)) r ((contDiffAt_const.prodMk contDiffAt_id).prodMk (A_analytic he))
lemma label_spec {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    ReferenceCharacteristic.A ((label a t κ r,κ),r)=A a t r :=
  QuadraticFit.label_spec (radius_pos he) (A_abs_lt he)
lemma label_J {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    ReferenceCharacteristic.J ((label a t κ r,κ),r)=j a t κ r := by
  symm
  apply QuadraticFit.slope_eq (radius_pos he) (m_abs_lt he)
  have hh := label_spec (κ:=κ) he
  change H ((ReferenceCharacteristic.J ((label a t κ r,κ),r),κ),r)/r=m a t r/r at hh
  exact (div_left_inj' (radius_pos he).ne').mp hh
lemma label_deriv {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    HasDerivAt (label a t κ) (err a t κ r*(1-(A a t r)^2)/ReferenceCharacteristic.Az ((label a t κ r,κ),r)) r := by
  have hz := (label_analytic (κ:=κ) he).differentiableAt (by simp)
  have hd := (ReferenceCharacteristic.A_analytic (q:=((label a t κ r,κ),r)) (radius_pos he)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f:=fun s=>((label a t κ s,κ),s)) r
      ((hz.hasDerivAt.prodMk (hasDerivAt_const r κ)).prodMk (hasDerivAt_id r))
  have hev : (fun s=>ReferenceCharacteristic.A ((label a t κ s,κ),s)) =ᶠ[𝓝 r] A a t := by
    filter_upwards [adm_eventually he] with s hs
    exact label_spec hs
  have hq := hd.unique ((A_deriv he).congr_of_eventuallyEq hev)
  rw [fderiv_model] at hq
  have hs := (ReferenceCharacteristic.A_analytic (q:=((label a t κ r,κ),r)) (radius_pos he)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r (label a t κ r,κ)).prodMk (hasDerivAt_id r))
  have hs' := hs.unique (ReferenceCharacteristic.A_deriv (radius_pos he))
  change direction ((0,0),1) ReferenceCharacteristic.A ((label a t κ r,κ),r)=_ at hs'
  rw [hs',label_spec he,label_J he] at hq
  have hn := (ReferenceCharacteristic.Az_pos (z:=label a t κ r) (k:=κ) (radius_pos he)).ne'
  have heq : deriv (label a t κ) r=err a t κ r*(1-(A a t r)^2)/ReferenceCharacteristic.Az ((label a t κ r,κ),r) := by
    apply (eq_div_iff hn).mpr
    dsimp only [ReferenceCharacteristic.Az,err] at hq ⊢
    linarith
  rw [←heq]
  exact hz.hasDerivAt
end QuinticLienard.ActualCharacteristic

end OAI
