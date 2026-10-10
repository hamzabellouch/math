import OAI.Geometry.SurfaceImmersion.Whitney.TransverseRuledSurface

namespace OAI

/-! The actual transverse ruling commutes with a linear target chart. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma ruling_linear_target (L : V →L[ℝ] W) {f : Base → V}
    (hf : ContDiff ℝ ∞ f) (x : Base) :
    transverseRuling (L ∘ f) x = L (transverseRuling f x) := by
  rw [transverseRuling,transverseRuling,axisValue,axisValue,axisTransverse,axisTransverse,
    fderiv_comp _ L.differentiableAt (hf.differentiable (by simp) _),L.fderiv]
  simp only [Function.comp_apply,ContinuousLinearMap.comp_apply,map_add,map_smul]

lemma regular_axis_transverse {f : Base → V} (hf : ContDiff ℝ ∞ f) {t : ℝ}
    (hI : Function.Injective (fderiv ℝ f (crosscapAxis t))) :
    deriv (axisValue f) t ≠ 0 ∧ ∀ r : ℝ, r • deriv (axisValue f) t ≠ axisTransverse f t := by
  rw [axisValue_deriv hf]
  constructor
  · intro hz
    have he := hI (hz.trans (map_zero _).symm)
    have hh := congrFun he 1
    norm_num at hh
  · intro r he
    have hh : fderiv ℝ f (crosscapAxis t) (r • (![0,1] : Base)) =
        fderiv ℝ f (crosscapAxis t) (![1,0] : Base) := by
      rw [map_smul]
      exact he
    have hc := congrFun (hI hh) 0
    norm_num at hc

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
