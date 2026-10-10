import OAI.Geometry.SurfaceImmersion.Geometry.GenericProjectionParameter

namespace OAI

/-! The derivative of a graph-direction coordinate. At a projection kernel
its derivative is exactly the projected derivative divided by the height. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def tangentRayVelocity (b : Bool) : Base :=
  if b then ![1,0] else ![0,1]

lemma tangentRay_hasDerivAt (b : Bool) (t : ℝ) :
    HasDerivAt (tangentRay b) (tangentRayVelocity b) t := by
  apply hasDerivAt_pi.mpr
  intro i
  cases b <;> fin_cases i <;>
    first | exact hasDerivAt_id t | exact hasDerivAt_const t _

lemma tangentRayVelocity_ne_zero (b : Bool) : tangentRayVelocity b ≠ 0 := by
  cases b <;> intro h
  · have hh := congrFun h 1
    norm_num [tangentRayVelocity] at hh
  · have hh := congrFun h 0
    norm_num [tangentRayVelocity] at hh

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma hasFDerivAt_graph_slope {f : E → V × ℝ} {D : E →L[ℝ] V × ℝ} {x : E}
    (hf : HasFDerivAt f D x) (a : V) (hn : (f x).2 ≠ 0)
    (he : (f x).1 = (f x).2 • a) :
    HasFDerivAt (fun y => (f y).2⁻¹ • (f y).1)
      ((f x).2⁻¹ • (graphProjection a).comp D) x := by
  have h := ((hasFDerivAt_inv hn).comp x hf.snd).smul hf.fst
  convert h using 1
  · rfl
  ext v
  change (f x).2⁻¹ • ((D v).1-(D v).2 • a) =
    (f x).2⁻¹ • (D v).1 + ((D v).2 * (-((f x).2 ^ 2)⁻¹)) • (f x).1
  have hc : (D v).2 * (-((f x).2 ^ 2)⁻¹) * (f x).2 =
      -((f x).2⁻¹ * (D v).2) := by
    field_simp
  rw [he,smul_smul,hc,neg_smul,smul_sub,smul_smul,sub_eq_add_neg]

lemma fderiv_graph_slope {f : E → V × ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (a : V) (hn : (f x).2 ≠ 0)
    (he : (f x).1 = (f x).2 • a) :
    fderiv ℝ (fun y => (f y).2⁻¹ • (f y).1) x =
      (f x).2⁻¹ • (graphProjection a).comp (fderiv ℝ f x) :=
  (hasFDerivAt_graph_slope hf.hasFDerivAt a hn he).fderiv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
