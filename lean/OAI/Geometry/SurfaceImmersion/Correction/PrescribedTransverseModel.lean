import OAI.Geometry.SurfaceImmersion.Whitney.TransverseRuledSurface

namespace OAI

/-! An actual smooth comparison map with any prescribed transverse
first derivative and the original values along the boundary axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def prescribedTransverseModel (f : Base → W) (b : ℝ → W) (x : Base) : W :=
  f x + x 0 • (b (x 1)-axisTransverse f (x 1))

lemma prescribedTransverseModel_smooth {f : Base → W} {b : ℝ → W}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (prescribedTransverseModel f b) :=
  hf.add ((contDiff_apply ℝ ℝ 0).smul
    ((hb.sub (axisTransverse_smooth hf)).comp (contDiff_apply ℝ ℝ 1)))

lemma prescribedTransverseModel_axis (f : Base → W) (b : ℝ → W) (t : ℝ) :
    prescribedTransverseModel f b (crosscapAxis t) = f (crosscapAxis t) := by
  simp [prescribedTransverseModel,crosscapAxis_apply]

lemma prescribedTransverseModel_first_jet {f : Base → W} {b : ℝ → W}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (t : ℝ) :
    fderiv ℝ (prescribedTransverseModel f b) (crosscapAxis t) =
      fderiv ℝ f (crosscapAxis t) +
      (ContinuousLinearMap.proj 0).smulRight (b t-axisTransverse f t) := by
  let a := crosscapAxis t
  have hdB := (((hb.sub (axisTransverse_smooth hf)).comp
    (contDiff_apply ℝ ℝ 1)).differentiable (by simp) a).hasFDerivAt
  have hd := (hf.differentiable (by simp) a).hasFDerivAt.add
    ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) a).smul hdB)
  change HasFDerivAt (prescribedTransverseModel f b) _ a at hd
  rw [hd.fderiv]
  simp [a,crosscapAxis_apply]

lemma prescribedTransverseModel_transverse {f : Base → W} {b : ℝ → W}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (t : ℝ) :
    axisTransverse (prescribedTransverseModel f b) t = b t := by
  rw [axisTransverse,prescribedTransverseModel_first_jet hf hb]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,Matrix.cons_val_zero,one_smul]
  change axisTransverse f t + (b t-axisTransverse f t) = b t
  abel

lemma prescribedTransverseModel_eq {f : Base → W} {b : ℝ → W} {x : Base}
    (hb : b (x 1) = axisTransverse f (x 1)) : prescribedTransverseModel f b x = f x := by
  simp only [prescribedTransverseModel,hb,sub_self,smul_zero,add_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
