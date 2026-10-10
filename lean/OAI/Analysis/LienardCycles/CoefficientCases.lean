import OAI.Analysis.LienardCycles.AxisReflection

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
noncomputable def reflectX (a : Fin 6 → ℝ) : Fin 6 → ℝ := ![a 0,-a 1,a 2,-a 3,a 4,-a 5]
@[simp] lemma reflectX_one (a : Fin 6 → ℝ) : reflectX a 1= -a 1 := rfl
@[simp] lemma reflectX_two (a : Fin 6 → ℝ) : reflectX a 2=a 2 := rfl
@[simp] lemma reflectX_three (a : Fin 6 → ℝ) : reflectX a 3= -a 3 := rfl
@[simp] lemma reflectX_four (a : Fin 6 → ℝ) : reflectX a 4=a 4 := rfl
@[simp] lemma reflectX_five (a : Fin 6 → ℝ) : reflectX a 5= -a 5 := rfl
lemma reflectX_poly (a : Fin 6 → ℝ) (x : ℝ) : poly (reflectX a) x=poly a (-x) := by
  simp [reflectX,poly]
  ring
lemma slope_formula (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    slope a h=a 1/root h+2*a 2+3*a 3*root h+4*a 4*(root h)^2+5*a 5*(root h)^3 := by
  dsimp [slope,c₁]
  field_simp [(root_pos hh).ne']
lemma curvature_formula (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    curvature a h=8*a 4+(-a 1+3*a 3*(root h)^2+15*a 5*(root h)^4)/(root h)^3 := by
  dsimp [curvature,c₁,c₂]
  field_simp [(root_pos hh).ne']
  ring
lemma intercept_formula (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    h*curvature a h-slope a h+2*a 2=
      (-3*a 1-3*a 3*(root h)^2+5*a 5*(root h)^4)/(2*root h) := by
  rw [curvature_formula a hh,slope_formula a hh]
  have he : h=(root h)^2/2 := by rw [root_sq hh.le]; ring
  nth_rw 1 [he]
  field_simp [(root_pos hh).ne']
  ring
lemma reflectX_third (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) : third (reflectX a) h= -third a h := by
  rw [third_formula _ hh,third_formula _ hh]
  simp only [reflectX_one,reflectX_three,reflectX_five]
  ring
lemma reflectX_curvature (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    curvature (reflectX a) h=16*a 4-curvature a h := by
  rw [curvature_formula _ hh,curvature_formula _ hh]
  simp only [reflectX_one,reflectX_three,reflectX_four,reflectX_five]
  ring
lemma reflectX_intercept (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    h*curvature (reflectX a) h-slope (reflectX a) h+2*a 2= -(h*curvature a h-slope a h+2*a 2) := by
  have h2 : reflectX a 2=a 2 := rfl
  rw [←h2,intercept_formula _ hh,h2,intercept_formula _ hh]
  simp only [reflectX_one,reflectX_three,reflectX_five]
  ring
lemma third_pos_case2 {a : Fin 6 → ℝ} (h1 : 0≤a 1) (h3 : a 3<0) (h5 : 0≤a 5)
    {h : ℝ} (hh : 0<h) : 0<third a h := by
  rw [third_formula a hh]
  have H : 0< -a 3*(root h)^2 := mul_pos (neg_pos.mpr h3) (pow_pos (root_pos hh) _)
  have H5 : 0≤5*a 5*(root h)^4 := by positivity
  exact div_pos (by nlinarith) (pow_pos (root_pos hh) _)
lemma curvature_lower_case3 {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : 0≤a 3) (h5 : 0≤a 5)
    {h T : ℝ} (hh : 0<h) (hT : h<T) :
    8*a 4+(-a 1)/(root T)^3≤curvature a h := by
  rw [curvature_formula a hh]
  have hx : root h≤root T := Real.sqrt_le_sqrt (by linarith)
  have hx3 : (root h)^3≤(root T)^3 := pow_le_pow_left₀ (root_pos hh).le hx _
  have hdiv := div_le_div_of_nonneg_left (neg_pos.mpr h1).le (pow_pos (root_pos hh) _) hx3
  have hnum : -a 1≤ -a 1+3*a 3*(root h)^2+15*a 5*(root h)^4 := by
    have H3 : 0≤3*a 3*(root h)^2 := by positivity
    have H5 : 0≤15*a 5*(root h)^4 := by positivity
    linarith
  exact add_le_add_right (hdiv.trans (div_le_div_of_nonneg_right hnum (pow_pos (root_pos hh) _).le)) _
lemma intercept_pos_case4 {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : a 3<0) (h5 : 0≤a 5)
    {h : ℝ} (hh : 0<h) : 0<h*curvature a h-slope a h+2*a 2 := by
  rw [intercept_formula a hh]
  have H : 0< -3*a 1 := by linarith
  have H3 : 0≤ -3*a 3*(root h)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have H5 : 0≤5*a 5*(root h)^4 := by positivity
  exact div_pos (by nlinarith) (mul_pos (by norm_num) (root_pos hh))
lemma root_tendsto_zero : Tendsto root (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous root := Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
  have hc0 : Tendsto root (𝓝 (0:ℝ)) (𝓝 0) := by
    have H : Tendsto root (𝓝 (0:ℝ)) (𝓝 (root 0)) := hc.continuousAt
    simpa [root] using H
  exact hc0.mono_left inf_le_left
lemma root_tendsto_zero_pos : Tendsto root (𝓝[>] (0:ℝ)) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨root_tendsto_zero,(show ∀ᶠ h : ℝ in 𝓝[>] 0, 0<h from self_mem_nhdsWithin).mono fun _ hh=>root_pos hh⟩
lemma slope_rest_limit (a : Fin 6 → ℝ) :
    Tendsto (fun h=>2*a 2+3*a 3*root h+4*a 4*(root h)^2+5*a 5*(root h)^3)
      (𝓝[>] (0:ℝ)) (𝓝 (2*a 2)) := by
  simpa using ((tendsto_const_nhds.add (root_tendsto_zero.const_mul (3*a 3))).add
    ((root_tendsto_zero.pow 2).const_mul (4*a 4))).add
      ((root_tendsto_zero.pow 3).const_mul (5*a 5))
lemma slope_atBot {a : Fin 6 → ℝ} (h1 : a 1<0) : Tendsto (slope a) (𝓝[>] (0:ℝ)) atBot := by
  have hi := tendsto_inv_nhdsGT_zero.comp root_tendsto_zero_pos
  have ht := (hi.const_mul_atTop_of_neg h1).atBot_add (slope_rest_limit a)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [slope_formula a hh,div_eq_mul_inv]
  simp only [Function.comp_apply]
  ring
lemma slope_atTop {a : Fin 6 → ℝ} (h1 : 0<a 1) : Tendsto (slope a) (𝓝[>] (0:ℝ)) atTop := by
  have hi := tendsto_inv_nhdsGT_zero.comp root_tendsto_zero_pos
  have ht := (hi.const_mul_atTop h1).atTop_add (slope_rest_limit a)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [slope_formula a hh,div_eq_mul_inv]
  simp only [Function.comp_apply]
  ring
end QuinticLienard.ScaledProfile

end OAI
