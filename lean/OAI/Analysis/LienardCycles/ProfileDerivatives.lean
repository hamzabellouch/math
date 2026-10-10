import OAI.Analysis.LienardCycles.ActualSmallWidth

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
lemma root_pos {h : ℝ} (hh : 0<h) : 0<root h := Real.sqrt_pos.mpr (by positivity)
lemma root_sq {h : ℝ} (hh : 0≤h) : (root h)^2=2*h := Real.sq_sqrt (by positivity)
lemma root_analytic {h : ℝ} (hh : 0<h) : ContDiffAt ℝ ω root h :=
  (contDiffAt_const.mul contDiffAt_id).sqrt (mul_ne_zero (by norm_num) hh.ne')
lemma root_hasDerivAt {h : ℝ} (hh : 0<h) : HasDerivAt root (1/root h) h := by
  have hd := (Real.hasDerivAt_sqrt (mul_ne_zero (by norm_num : (2:ℝ)≠0) hh.ne')).comp h
    ((hasDerivAt_id h).const_mul 2)
  convert! hd using 1
  simp only [root]
  ring
lemma poly_hasDerivAt (a : Fin 6 → ℝ) (x : ℝ) : HasDerivAt (poly a) (c₁ a x) x := by
  have hd := (hasDerivAt_const x (a 0)).add (((hasDerivAt_id x).const_mul (a 1))) |>.add
    (((hasDerivAt_id x).pow 2).const_mul (a 2)) |>.add
    (((hasDerivAt_id x).pow 3).const_mul (a 3)) |>.add
    (((hasDerivAt_id x).pow 4).const_mul (a 4)) |>.add
    (((hasDerivAt_id x).pow 5).const_mul (a 5))
  convert! hd using 1
  dsimp [c₁]
  ring
lemma c₁_hasDerivAt (a : Fin 6 → ℝ) (x : ℝ) : HasDerivAt (c₁ a) (2*c₂ a x) x := by
  have hd := (hasDerivAt_const x (a 1)).add ((hasDerivAt_id x).const_mul (2*a 2)) |>.add
    (((hasDerivAt_id x).pow 2).const_mul (3*a 3)) |>.add
    (((hasDerivAt_id x).pow 3).const_mul (4*a 4)) |>.add
    (((hasDerivAt_id x).pow 4).const_mul (5*a 5))
  convert! hd using 1
  dsimp [c₂]
  ring
lemma c₂_hasDerivAt (a : Fin 6 → ℝ) (x : ℝ) : HasDerivAt (c₂ a) (3*c₃ a x) x := by
  have hd := (hasDerivAt_const x (a 2)).add ((hasDerivAt_id x).const_mul (3*a 3)) |>.add
    (((hasDerivAt_id x).pow 2).const_mul (6*a 4)) |>.add
    (((hasDerivAt_id x).pow 3).const_mul (10*a 5))
  convert! hd using 1
  dsimp [c₃]
  ring
lemma profile_hasDerivAt (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun u => poly a (root u)) (slope a h) h := by
  simpa only [slope,mul_one_div] using! (poly_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)
lemma slope_hasDerivAt (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (slope a) (curvature a h) h := by
  have hx := root_pos hh
  have hd := ((c₁_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)).div (root_hasDerivAt hh) hx.ne'
  convert! hd using 1
  dsimp [curvature]
  field_simp
lemma curvature_hasDerivAt (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (curvature a) (third a h) h := by
  have hx := root_pos hh
  have hd := ((((c₂_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)).const_mul 2).div
    ((root_hasDerivAt hh).pow 2) (pow_ne_zero _ hx.ne')).sub
      (((c₁_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)).div
        ((root_hasDerivAt hh).pow 3) (pow_ne_zero _ hx.ne'))
  convert! hd using 1
  rw [third_formula a hh]
  dsimp [c₁,c₂,c₃]
  field_simp
  ring
lemma slope_analytic (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) : ContDiffAt ℝ ω (slope a) h := by
  have hr := root_analytic hh
  change ContDiffAt ℝ ω (fun u => (a 1+2*a 2*root u+3*a 3*(root u)^2+4*a 4*(root u)^3+5*a 5*(root u)^4)/root u) h
  fun_prop (disch:=exact (root_pos hh).ne')
lemma curvature_analytic (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) : ContDiffAt ℝ ω (curvature a) h := by
  have hr := root_analytic hh
  change ContDiffAt ℝ ω (fun u => 2*(a 2+3*a 3*root u+6*a 4*(root u)^2+10*a 5*(root u)^3)/(root u)^2-(a 1+2*a 2*root u+3*a 3*(root u)^2+4*a 4*(root u)^3+5*a 5*(root u)^4)/(root u)^3) h
  fun_prop (disch:=exact pow_ne_zero _ (root_pos hh).ne')
end QuinticLienard.ScaledProfile

end OAI
