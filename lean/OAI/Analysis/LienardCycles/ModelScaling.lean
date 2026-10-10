import OAI.Analysis.LienardCycles.PositiveScaling

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PolynomialModel ArchSymmetries WidthCoordinates
lemma scaling_width (d k : ℝ) {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    H ((d,k),r*s)=r*H ((r*d,r^3*k),s) := by
  have hh := (fixed_width_affine profile profile_contDiff model_local_flow
    (p := (r*d,r^3*k)) (q := (d,k)) (h:=0) (H:=0) (C:=0) hs hr
    (by intro x; dsimp [profile]; ring)).2
  simpa [H] using hh
lemma Hr_scaling (d k : ℝ) {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    Hr ((d,k),r*s)=Hr ((r*d,r^3*k),s) := by
  have hd := (Hr_hasDerivAt (d:=d) (k:=k) (mul_pos hr hs)).comp s
    ((hasDerivAt_id s).const_mul r)
  have he := (Hr_hasDerivAt (d:=r*d) (k:=r^3*k) hs).const_mul r
  have hev : (fun t => H ((d,k),r*t)) =ᶠ[𝓝 s] (fun t => r*H ((r*d,r^3*k),t)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hs] with t ht
    exact scaling_width d k hr ht
  have hc := hd.unique (he.congr_of_eventuallyEq hev)
  apply mul_right_cancel₀ hr.ne'
  calc
    _ = r*Hr ((r*d,r^3*k),s) := by simpa only [mul_one] using hc
    _ = _ := mul_comm _ _
end QuinticLienard.QuadraticCoordinates
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates
lemma fit_scaled {r M v : ℝ} (hr : 0<r) (hM : |M|<r) (hv : |v|<1) :
    fitD ((1,M/r),v)=r*fitD ((r,M),v) ∧ fitK ((1,M/r),v)=r^3*fitK ((r,M),v) := by
  have hMr : |M/r|<1 := by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hM
  have hs := fit_spec hr hM hv
  have hh := scaling_width (fitD ((r,M),v)) (fitK ((r,M),v)) hr (by norm_num : (0:ℝ)<1)
  have hh' : H ((r*fitD ((r,M),v),r^3*fitK ((r,M),v)),1)=M/r := by
    rw [mul_one,hs.1] at hh
    apply (eq_div_iff hr.ne').mpr
    simpa only [mul_comm] using hh.symm
  have hh'' := Hr_scaling (fitD ((r,M),v)) (fitK ((r,M),v)) hr (by norm_num : (0:ℝ)<1)
  rw [mul_one,hs.2] at hh''
  exact fit_unique (by norm_num) hMr hv hh' hh''.symm
end QuinticLienard.QuadraticFit

end OAI
