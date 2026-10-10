import OAI.Geometry.Immersion.ClosedSurface.SecondForms
import OAI.Geometry.Immersion.ClosedSurface.ForcedModes

namespace OAI

/-! Coordinate metric derivatives needed for the intrinsic Gauss expression.
The third derivatives cancel before any estimate is made. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma real_partial_dot {n : ℕ} {F G : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q ⬝ᵥ G q) p =
      coordDeriv v F p ⬝ᵥ G p+F p ⬝ᵥ coordDeriv v G p := by
  have hf (i : Fin n) := ((ContinuousLinearMap.proj i : RVec n →L[ℝ] ℝ).hasFDerivAt.comp p
    hF.hasFDerivAt)
  have hg (i : Fin n) := ((ContinuousLinearMap.proj i : RVec n →L[ℝ] ℝ).hasFDerivAt.comp p
    hG.hasFDerivAt)
  have hs := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hf i).fun_mul (hg i)).fderiv
  simp only [Function.comp_def,ContinuousLinearMap.proj_apply] at hs
  unfold coordDeriv dotProduct
  rw [hs]
  simp only [sum_apply,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma real_dot_smooth {n : ℕ} {F G : RField n}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q => F q ⬝ᵥ G q) :=
  ContDiff.sum (fun i _ => (contDiff_pi.mp hF i).mul (contDiff_pi.mp hG i))

lemma realMetric_partial {F : RField 4} (hF : ContDiff ℝ ∞ F) (p d v w : Base) :
    coordDeriv d (realMetric F v w) p =
      coordDeriv d (coordDeriv v F) p ⬝ᵥ coordDeriv w F p+
      coordDeriv v F p ⬝ᵥ coordDeriv d (coordDeriv w F) p :=
  real_partial_dot ((contDiff_real_coordDeriv hF v).differentiable (by simp) p)
    ((contDiff_real_coordDeriv hF w).differentiable (by simp) p) d

lemma realMetric_second_partial {F : RField 4} (hF : ContDiff ℝ ∞ F) (p d e v w : Base) :
    coordDeriv d (coordDeriv e (realMetric F v w)) p =
      coordDeriv d (coordDeriv e (coordDeriv v F)) p ⬝ᵥ coordDeriv w F p+
      coordDeriv e (coordDeriv v F) p ⬝ᵥ coordDeriv d (coordDeriv w F) p+
      (coordDeriv d (coordDeriv v F) p ⬝ᵥ coordDeriv e (coordDeriv w F) p+
      coordDeriv v F p ⬝ᵥ coordDeriv d (coordDeriv e (coordDeriv w F)) p) := by
  have hv := contDiff_real_coordDeriv hF v
  have hw := contDiff_real_coordDeriv hF w
  have hev := contDiff_real_coordDeriv hv e
  have hew := contDiff_real_coordDeriv hw e
  have he : coordDeriv e (realMetric F v w) = fun q =>
      coordDeriv e (coordDeriv v F) q ⬝ᵥ coordDeriv w F q+
      coordDeriv v F q ⬝ᵥ coordDeriv e (coordDeriv w F) q :=
    funext fun q => realMetric_partial hF q e v w
  rw [he,partial_add ((real_dot_smooth hev hw).differentiable (by simp) p)
    ((real_dot_smooth hv hew).differentiable (by simp) p),
    real_partial_dot (hev.differentiable (by simp) p) (hw.differentiable (by simp) p),
    real_partial_dot (hv.differentiable (by simp) p) (hew.differentiable (by simp) p)]

/-- The raw second-derivative Gauss expression only uses second metric jets. -/
theorem raw_gauss_metric_identity {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    coordDeriv dx (coordDeriv dx F) p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p-
      coordDeriv dx (coordDeriv dy F) p ⬝ᵥ coordDeriv dx (coordDeriv dy F) p =
    (2*coordDeriv dx (coordDeriv dy (realMetric F dx dy)) p-
      coordDeriv dy (coordDeriv dy (realMetric F dx dx)) p-
      coordDeriv dx (coordDeriv dx (realMetric F dy dy)) p)/2 := by
  have hcomm : coordDeriv dy (coordDeriv dx F) = coordDeriv dx (coordDeriv dy F) :=
    funext fun q => real_second_coordDeriv_comm hF q dy dx
  have hthird : coordDeriv dy (coordDeriv dx (coordDeriv dy F)) =
      coordDeriv dx (coordDeriv dy (coordDeriv dy F)) :=
    funext fun q => real_second_coordDeriv_comm (contDiff_real_coordDeriv hF dy) q dy dx
  simp only [realMetric_second_partial hF,hcomm,hthird]
  rw [dotProduct_comm (coordDeriv dx (coordDeriv dx (coordDeriv dy F)) p),
    dotProduct_comm (coordDeriv dx (coordDeriv dy (coordDeriv dy F)) p)]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
