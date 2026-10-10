import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselLogIntegrable
import OAI.NumberTheory.CubicMoment.Estimates.ThetaHeatKernelBound
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Differentiation of the fixed cubic Bessel integral in logarithmic
coordinates, with an integrable local majorant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicBesselLogDerivative (a u : ℝ) : ℝ :=
  -2*Real.cosh u*cubicBesselLogWeight a u

lemma cubicBesselLogWeight_hasDerivAt (a u : ℝ) :
    HasDerivAt (fun x => cubicBesselLogWeight x u) (cubicBesselLogDerivative a u) a := by
  have h := (((hasDerivAt_id a).const_mul (-2*Real.cosh u)).exp).const_mul (Real.exp (-u/3))
  simp only [id_eq] at h
  have he (x : ℝ) : Real.exp (-2*x*Real.cosh u)=Real.exp (-2*Real.cosh u*x) := by
    congr 1
    ring
  convert h using 1
  · funext x
    unfold cubicBesselLogWeight
    rw [he]
  · unfold cubicBesselLogDerivative cubicBesselLogWeight
    rw [he]
    ring

lemma cubicBesselLogDerivative_bound {a b : ℝ} (hb : 0<b) (hab : 2*b≤a) (u : ℝ) :
    ‖cubicBesselLogDerivative a u‖≤(1/b)*cubicBesselLogWeight b u := by
  let y := 2*Real.cosh u
  have hy : 0<y := mul_pos (by norm_num) (Real.cosh_pos u)
  have hp := power_exp_bound hb 1 y hy.le
  norm_num only [pow_one,Nat.factorial_one,Nat.cast_one] at hp
  have he : Real.exp (-a*y)≤Real.exp (-2*b*y) := Real.exp_le_exp.mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left he hy.le
  have hsplit : y*Real.exp (-2*b*y)=(y*Real.exp (-b*y))*Real.exp (-b*y) := by
    have he : Real.exp (-2*b*y)=Real.exp (-b*y)*Real.exp (-b*y) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  rw [hsplit] at hmul
  have hp' := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-b*y)).le
  have h := mul_le_mul_of_nonneg_left (hmul.trans hp') (Real.exp_pos (-u/3)).le
  unfold cubicBesselLogDerivative cubicBesselLogWeight
  rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_neg (by norm_num : (-2:ℝ)<0),
    Real.norm_of_nonneg (Real.cosh_pos u).le,
    Real.norm_of_nonneg (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le]
  dsimp [y] at h
  convert h using 1 <;> ring_nf

lemma cubicBesselLogDerivative_integrable {a : ℝ} (ha : 0<a) :
    Integrable (cubicBesselLogDerivative a) := by
  have hb : 0<a/2 := by linarith
  apply ((cubicBesselLogWeight_integrable hb).const_mul (1/(a/2))).mono'
    (by unfold cubicBesselLogDerivative cubicBesselLogWeight; fun_prop)
  exact Filter.Eventually.of_forall (cubicBesselLogDerivative_bound hb (by linarith))

theorem cubicBesselLogIntegral_hasDerivAt {a : ℝ} (ha : 0<a) :
    HasDerivAt (fun x => ∫ u : ℝ,cubicBesselLogWeight x u)
      (∫ u : ℝ,cubicBesselLogDerivative a u) a := by
  have hb : 0<a/4 := by linarith
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Ioi (a/2)) (bound:=fun u => (1/(a/4))*cubicBesselLogWeight (a/4) u)
    (isOpen_Ioi.mem_nhds (by change a/2<a; linarith))
    (Filter.Eventually.of_forall (fun x => by
      unfold cubicBesselLogWeight; fun_prop))
    (cubicBesselLogWeight_integrable ha) ?_ ?_
    ((cubicBesselLogWeight_integrable hb).const_mul (1/(a/4))) ?_).2
  · unfold cubicBesselLogDerivative cubicBesselLogWeight
    fun_prop
  · exact Filter.Eventually.of_forall (fun u x hx =>
      cubicBesselLogDerivative_bound hb (by change a/2<x at hx; linarith) u)
  · exact Filter.Eventually.of_forall (fun u x _ => cubicBesselLogWeight_hasDerivAt x u)

end CubicFirstMoment

end

end OAI
