import OAI.Geometry.SurfaceImmersion.Whitney.HomotopyCollarDerivative
import OAI.Geometry.SurfaceImmersion.Whitney.TransverseRuledSurface

namespace OAI

/-! Exact interpolation of two surface germs with the same boundary
curve; their flat remainders are retained rather than discarded. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def collarRemainder (f : Base → W) : Base → W := f - transverseRuling f

def exactCollarInterpolation (f g : Base → W) (V : ℝ × ℝ → W)
    (χ : ℝ → ℝ) (x : Base) : W :=
  homotopyCollar (fun t => f (crosscapAxis t)) V χ x + collarRemainder f x +
    χ (x 0) • (collarRemainder g x - collarRemainder f x)

lemma collarRemainder_smooth {f : Base → W} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (collarRemainder f) := hf.sub (transverseRuling_smooth hf)

lemma collarRemainder_axis (f : Base → W) (t : ℝ) :
    collarRemainder f (crosscapAxis t) = 0 := by
  simp [collarRemainder,transverseRuling_axis]

lemma collarRemainder_first_jet {f : Base → W} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    fderiv ℝ (collarRemainder f) (crosscapAxis t) = 0 := by
  rw [show collarRemainder f = f - transverseRuling f from rfl,
    fderiv_sub (hf.differentiable (by simp) _)
      ((transverseRuling_smooth hf).differentiable (by simp) _),
    transverseRuling_first_jet hf,sub_self]

lemma exactCollarInterpolation_smooth {f g : Base → W} {V : ℝ × ℝ → W} {χ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hV : ContDiff ℝ ∞ V) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (exactCollarInterpolation f g V χ) :=
  ((homotopyCollar_smooth (hf.comp crosscapAxis.contDiff) hV hχ).add
    (collarRemainder_smooth hf)).add
    ((hχ.comp (contDiff_apply ℝ ℝ 0)).smul
      ((collarRemainder_smooth hg).sub (collarRemainder_smooth hf)))

lemma exactCollarInterpolation_zero {f g : Base → W} {V : ℝ × ℝ → W} {χ : ℝ → ℝ}
    (hV : ∀ t, V (0,t) = fderiv ℝ f (crosscapAxis t) ![1,0])
    {x : Base} (hx : χ (x 0) = 0) : exactCollarInterpolation f g V χ x = f x := by
  simp only [exactCollarInterpolation,homotopyCollar,hx,hV,zero_smul,add_zero,
    collarRemainder,Pi.sub_apply,transverseRuling,axisValue,axisTransverse]
  abel

lemma exactCollarInterpolation_one {f g : Base → W} {V : ℝ × ℝ → W} {χ : ℝ → ℝ}
    (hc : ∀ t, f (crosscapAxis t) = g (crosscapAxis t))
    (hV : ∀ t, V (1,t) = fderiv ℝ g (crosscapAxis t) ![1,0])
    {x : Base} (hx : χ (x 0) = 1) : exactCollarInterpolation f g V χ x = g x := by
  simp only [exactCollarInterpolation,homotopyCollar,hx,hV,one_smul,hc,
    collarRemainder,Pi.sub_apply,transverseRuling,axisValue,axisTransverse]
  abel

lemma exactCollarInterpolation_stationary {f g : Base → W} {V : ℝ × ℝ → W} {χ : ℝ → ℝ}
    {x : Base} (hx : g x = f x)
    (hc : g (crosscapAxis (x 1)) = f (crosscapAxis (x 1)))
    (ht : axisTransverse g (x 1) = axisTransverse f (x 1))
    (hV : V (χ (x 0),x 1) = axisTransverse f (x 1)) :
    exactCollarInterpolation f g V χ x = f x := by
  simp only [exactCollarInterpolation, homotopyCollar, hV, collarRemainder,
    Pi.sub_apply, transverseRuling, ht, axisValue, hc, hx]
  module

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
