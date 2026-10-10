import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Differentiate the fixed order-one-third heat integral on its positive
axis. The dominating inverse Laplace moment is integrable there. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicBesselHeatDerivative (x t : ℝ) : ℝ := -cubicBesselHeat x t/t

lemma cubicBesselHeat_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y => cubicBesselHeat y t) (cubicBesselHeatDerivative x t) x := by
  have h := (((hasDerivAt_id x).neg.div_const t).exp).const_mul
    (t^(-4/3:ℝ)*Real.exp (-t))
  simp only [Pi.neg_apply,id_eq] at h
  convert h using 1
  · rfl
  · unfold cubicBesselHeatDerivative cubicBesselHeat
    ring

lemma cubicBesselHeatDerivative_local_bound {a x t : ℝ} (hax : a≤x) (ht : 0<t) :
    ‖cubicBesselHeatDerivative x t‖≤t^(-7/3:ℝ)*Real.exp (-a/t) := by
  have h := div_le_div_of_nonneg_right (cubicBesselHeat_local_bound hax ht) ht.le
  have he : t^(-4/3:ℝ)/t=t^(-7/3:ℝ) := by
    calc
      _ = t^(-4/3:ℝ)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((-4/3:ℝ)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by norm_num
  simpa only [cubicBesselHeatDerivative,norm_div,norm_neg,Real.norm_eq_abs,
    abs_of_pos ht,mul_div_right_comm,he] using h

lemma cubicBesselHeat_integral_hasDerivAt {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y => ∫ t in Ioi (0:ℝ),cubicBesselHeat y t)
      (∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t) x := by
  have hi : IntegrableOn (fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-(x/2)/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ)<4/3)
      (show 0<x/2 by positivity) using 1
    norm_num
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Ioi (x/2)) (bound:=fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-(x/2)/t))
    (isOpen_Ioi.mem_nhds (by change x/2<x; linarith))
    (Eventually.of_forall (fun y => by
      apply Measurable.aestronglyMeasurable
      unfold cubicBesselHeat
      fun_prop)) (cubicBesselHeat_integrable hx) ?_ ?_ hi ?_).2
  · apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeatDerivative cubicBesselHeat
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    exact cubicBesselHeatDerivative_local_bound hy.le ht
  · filter_upwards with t
    intro y _
    exact cubicBesselHeat_hasDerivAt y t

def cubicBesselKernelDerivative (x : ℝ) : ℝ :=
  ((1/6:ℝ)*x^(-5/6:ℝ))*(∫ t in Ioi (0:ℝ),cubicBesselHeat x t)+
    x^(1/6:ℝ)*(∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t)

theorem cubicBesselKernel_hasDerivAt {x : ℝ} (hx : 0<x) :
    HasDerivAt cubicBesselKernel (cubicBesselKernelDerivative x) x := by
  have hp := Real.hasDerivAt_rpow_const (x:=x) (p:=(1/6:ℝ)) (Or.inl (ne_of_gt hx))
  have h := hp.mul (cubicBesselHeat_integral_hasDerivAt hx)
  convert h using 1
  · funext y
    rfl
  · norm_num [cubicBesselKernelDerivative]

theorem cubicBesselKernel_differentiableOn : DifferentiableOn ℝ cubicBesselKernel (Ioi 0) :=
  fun _ hx => (cubicBesselKernel_hasDerivAt hx).differentiableAt.differentiableWithinAt

end CubicFirstMoment

end

end OAI
