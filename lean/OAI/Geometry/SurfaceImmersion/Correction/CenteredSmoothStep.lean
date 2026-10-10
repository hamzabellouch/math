import OAI.Geometry.SurfaceImmersion.Geometry.RegularCurveGerms
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! A centered flat step with strict separation of opposite parameters,
used to round a tangential return between two disjoint curve branches. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def centeredSmoothStep (t : ℝ) : ℝ := Real.smoothTransition ((t+1)/2)

lemma centeredSmoothStep_smooth : ContDiff ℝ ∞ centeredSmoothStep :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const 2)

lemma centeredSmoothStep_zero {t : ℝ} (ht : t ≤ -1) : centeredSmoothStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma centeredSmoothStep_one {t : ℝ} (ht : 1 ≤ t) : centeredSmoothStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma centeredSmoothStep_bounds (t : ℝ) : centeredSmoothStep t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma expNegInvGlue_strict {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    expNegInvGlue x < expNegInvGlue y := by
  simp only [expNegInvGlue,not_le.mpr hx,not_le.mpr (hx.trans hxy),ite_false]
  apply Real.exp_lt_exp.mpr
  exact neg_lt_neg (inv_strictAnti₀ hx hxy)

lemma centeredSmoothStep_opposite_lt {t : ℝ} (ht : 0 < t) :
    centeredSmoothStep (-t) < centeredSmoothStep t := by
  let u := (t+1)/2
  let v := (-t+1)/2
  have hu : 0 < u := by dsimp [u]; linarith
  have hvu : v < u := by dsimp [u,v]; linarith
  have hev : expNegInvGlue v < expNegInvGlue u := by
    by_cases hv : 0 < v
    · exact expNegInvGlue_strict hv hvu
    · rw [expNegInvGlue.zero_of_nonpos (not_lt.mp hv)]
      exact expNegInvGlue.pos_of_pos hu
  have huv : 1-u = v := by dsimp [u,v]; ring
  have hvu' : 1-v = u := by dsimp [u,v]; ring
  change Real.smoothTransition v < Real.smoothTransition u
  rw [Real.smoothTransition,Real.smoothTransition,huv,hvu',add_comm (expNegInvGlue v)]
  exact div_lt_div_of_pos_right hev (Real.smoothTransition.pos_denom u |>.trans_eq (by rw [huv]))

lemma expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue ((x⁻¹)^2 * expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x

lemma centeredSmoothStep_hasDerivAt_zero : HasDerivAt centeredSmoothStep 1 0 := by
  let e := expNegInvGlue (1/2)
  have he : 0 < e := expNegInvGlue.pos_of_pos (by norm_num)
  have hE : HasDerivAt expNegInvGlue (4*e) (1/2) := by
    convert expNegInvGlue_hasDerivAt (1/2) using 1
    norm_num [e]
  have hL : HasDerivAt (fun t : ℝ => (t+1)/2) (1/2) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).add_const 1).div_const 2 using 1
    norm_num
  have hR : HasDerivAt (fun t : ℝ => 1-(t+1)/2) (-1/2) 0 := by
    convert hL.const_sub 1 using 1
    norm_num
  have hA : HasDerivAt (fun t : ℝ => expNegInvGlue ((t+1)/2)) (2*e) 0 := by
    have hE' : HasDerivAt expNegInvGlue (4*e) ((0+1)/2) := by
      convert hE using 1
      norm_num
    convert hE'.comp 0 hL using 1 <;> first | rfl | ring
  have hB : HasDerivAt (fun t : ℝ => expNegInvGlue (1-(t+1)/2)) (-2*e) 0 := by
    have hE' : HasDerivAt expNegInvGlue (4*e) (1-(0+1)/2) := by
      convert hE using 1
      norm_num
    convert hE'.comp 0 hR using 1 <;> first | rfl | ring
  have hD := hA.div (hA.add hB) (by
    norm_num only [Pi.add_apply,zero_add]
    change e+e ≠ 0
    positivity)
  convert hD using 1
  · rfl
  · norm_num only [Pi.add_apply,zero_add]
    change 1 = ((2*e)*(e+e)-e*(2*e+ -2*e))/(e+e)^2
    field_simp [ne_of_gt he]
    ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
