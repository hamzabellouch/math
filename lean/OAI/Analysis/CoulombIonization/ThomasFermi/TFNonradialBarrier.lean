import Mathlib
import OAI.Analysis.CoulombIonization.Model
import OAI.Analysis.CoulombIonization.FieldAnalysis.RadialPower

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

def tfCapBarrier (A R : ℝ) (x : Space) : ℝ := A*R^4/(R^2-‖x‖^2)^4

lemma capDenominator_pos {R : ℝ} {x : Space} (hx : ‖x‖ < R) :
    0 < R^2-‖x‖^2 := by nlinarith [norm_nonneg x]

lemma tfCapBarrier_pos {A R : ℝ} (hA : 0 < A) {x : Space} (hx : ‖x‖ < R) :
    0 < tfCapBarrier A R x := by
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  exact div_pos (mul_pos hA (pow_pos hR _)) (pow_pos (capDenominator_pos hx) _)

lemma cap_scalar_deriv_four (C d s : ℝ) (hne : d-s ≠ 0) :
    HasDerivAt (fun t : ℝ => C/(d-t)^4) (4*C/(d-s)^5) s := by
  convert! ((hasDerivAt_const s C).div (((hasDerivAt_const s d).sub (hasDerivAt_id s)).pow 4)
    (pow_ne_zero 4 hne)) using 1
  norm_num
  field_simp

lemma cap_scalar_deriv_five (C d s : ℝ) (hne : d-s ≠ 0) :
    HasDerivAt (fun t : ℝ => 4*C/(d-t)^5) (20*C/(d-s)^6) s := by
  convert! ((hasDerivAt_const s (4*C)).div (((hasDerivAt_const s d).sub (hasDerivAt_id s)).pow 5)
    (pow_ne_zero 5 hne)) using 1
  norm_num
  field_simp
  ring

lemma cap_scalar_second (C d s : ℝ) (hne : d-s ≠ 0) :
    deriv (deriv (fun t : ℝ => C/(d-t)^4)) s = 20*C/(d-s)^6 := by
  have he : deriv (fun t : ℝ => C/(d-t)^4) =ᶠ[𝓝 s] fun t => 4*C/(d-t)^5 := by
    filter_upwards [(continuous_const.sub continuous_id).continuousAt.eventually_ne hne] with t ht
    exact (cap_scalar_deriv_four C d t ht).deriv
  rw [he.deriv_eq,(cap_scalar_deriv_five C d s hne).deriv]

lemma tfCapBarrier_contDiffAt (A : ℝ) {R : ℝ} {x : Space} (hx : ‖x‖ < R) :
    ContDiffAt ℝ 2 (tfCapBarrier A R) x :=
  contDiffAt_const.div ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).pow 4)
    (pow_ne_zero _ (capDenominator_pos hx).ne')

lemma tfCapBarrier_laplacian (A : ℝ) {R : ℝ} {x : Space} (hx : ‖x‖ < R) :
    Δ (tfCapBarrier A R) x = A*R^4*(24*R^2+56*‖x‖^2)/(R^2-‖x‖^2)^6 := by
  have hn := (capDenominator_pos hx).ne'
  have hc : ContDiffAt ℝ 2 (fun s : ℝ => A*R^4/(R^2-s)^4) (‖x‖^2) :=
    contDiffAt_const.div ((contDiffAt_const.sub contDiffAt_id).pow 4) (pow_ne_zero _ hn)
  change Δ (fun x : Space => (fun s : ℝ => A*R^4/(R^2-s)^4) (‖x‖^2)) x = _
  rw [CoulombPDE.laplacian_norm_sq_comp hc,cap_scalar_second _ _ _ hn,
    (cap_scalar_deriv_four _ _ _ hn).deriv]
  norm_num [Space,finrank_euclideanSpace_fin]
  field_simp
  ring

lemma tfCapBarrier_reaction {A R : ℝ} (hA : 0 ≤ A) {x : Space} (hx : ‖x‖ < R) :
    (tfCapBarrier A R x)^(3/2:ℝ) = A^(3/2:ℝ)*R^6/(R^2-‖x‖^2)^6 := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx.le
  have hd := (capDenominator_pos hx).le
  rw [tfCapBarrier,Real.div_rpow (mul_nonneg hA (pow_nonneg hR _)) (pow_nonneg hd _),
    Real.mul_rpow hA (pow_nonneg hR _)]
  have hp (a : ℝ) (ha : 0 ≤ a) : (a^4)^(3/2:ℝ) = a^6 := by
    rw [←Real.rpow_natCast a 4,←Real.rpow_mul ha]
    norm_num
  rw [hp R hR,hp _ hd]

lemma tfCapBarrier_supersolution {A R k : ℝ} (hA : 0 < A)
    (hkA : 80*A ≤ k*A^(3/2:ℝ)) {x : Space} (hx : ‖x‖ < R) :
    Δ (tfCapBarrier A R) x ≤ k*(tfCapBarrier A R x)^(3/2:ℝ) := by
  rw [tfCapBarrier_laplacian A hx,tfCapBarrier_reaction hA.le hx]
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  have hd : 0 < (R^2-‖x‖^2)^6 := pow_pos (capDenominator_pos hx) _
  rw [←mul_div_assoc,div_le_div_iff_of_pos_right hd]
  have hn : ‖x‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg x) hx.le 2
  calc
    _ ≤ A*R^4*(80*R^2) := mul_le_mul_of_nonneg_left (by nlinarith)
      (mul_nonneg hA.le (pow_nonneg hR.le _))
    _ = (80*A)*R^6 := by ring
    _ ≤ (k*A^(3/2:ℝ))*R^6 := mul_le_mul_of_nonneg_right hkA (pow_nonneg hR.le _)
    _ = _ := by ring

end CoulombAnalysis

end

end OAI
