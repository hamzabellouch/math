import OAI.Geometry.SurfaceImmersion.Whitney.ActualRuledTargetTube
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace OAI

/-! An explicit immersed strip turning its transverse direction by a
 smooth angle, with the original longitudinal coordinate unchanged. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def twistedRuledCoordinates (θ : Base → ℝ) (x : Base) : Base × ℝ :=
  (![x 0*Real.cos (θ x),x 0*Real.sin (θ x)],x 1)

def twistedRuledDerivative (θ : Base → ℝ) (x : Base) : Base →L[ℝ] (Base × ℝ) :=
  (ContinuousLinearMap.pi ![
    Real.cos (θ x) • ContinuousLinearMap.proj 0 - (x 0*Real.sin (θ x)) • fderiv ℝ θ x,
    Real.sin (θ x) • ContinuousLinearMap.proj 0 + (x 0*Real.cos (θ x)) • fderiv ℝ θ x]).prod
      (ContinuousLinearMap.proj 1)

lemma twistedRuledCoordinates_smooth {θ : Base → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (twistedRuledCoordinates θ) := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [twistedRuledCoordinates] <;> fun_prop
  · exact contDiff_apply ℝ ℝ 1

lemma twistedRuledCoordinates_hasFDerivAt {θ : Base → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (x : Base) :
    HasFDerivAt (twistedRuledCoordinates θ) (twistedRuledDerivative θ x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have ht := (hθ.differentiable (by simp) x).hasFDerivAt
  apply HasFDerivAt.prodMk
  · apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert h0.mul ht.cos using 1
      · funext y; rfl
      · apply ContinuousLinearMap.ext
        intro v
        simp
        ring
    · convert h0.mul ht.sin using 1
      · funext y; rfl
      · apply ContinuousLinearMap.ext
        intro v
        simp
        ring
  · exact h1

lemma twistedRuledDerivative_apply (θ : Base → ℝ) (x v : Base) :
    twistedRuledDerivative θ x v =
      (![Real.cos (θ x)*v 0-x 0*Real.sin (θ x)*(fderiv ℝ θ x v),
        Real.sin (θ x)*v 0+x 0*Real.cos (θ x)*(fderiv ℝ θ x v)],v 1) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [twistedRuledDerivative]
  · rfl

lemma twistedRuledCoordinates_immersion {θ : Base → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (x : Base) :
    Function.Injective (fderiv ℝ (twistedRuledCoordinates θ) x) := by
  rw [(twistedRuledCoordinates_hasFDerivAt hθ x).fderiv]
  suffices hz : ∀ v : Base, twistedRuledDerivative θ x v = 0 → v = 0 by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hvw,sub_self]
  intro v hv
  rw [twistedRuledDerivative_apply] at hv
  have h1 : v 1 = 0 := congrArg Prod.snd hv
  have h0 := congrArg (fun z : Base × ℝ => z.1 0) hv
  have h2 := congrArg (fun z : Base × ℝ => z.1 1) hv
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Prod.fst_zero,Pi.zero_apply] at h0 h2
  have hs := Real.sin_sq_add_cos_sq (θ x)
  have hv0 : v 0 = 0 := by
    linear_combination Real.cos (θ x)*h0 + Real.sin (θ x)*h2 - v 0*hs
  ext i
  fin_cases i
  · exact hv0
  · exact h1

lemma twistedRuledCoordinates_axis (θ : Base → ℝ) (t : ℝ) :
    twistedRuledCoordinates θ (crosscapAxis t) = (0,t) := by
  simp [twistedRuledCoordinates,crosscapAxis_apply]

lemma twistedRuledCoordinates_zero {θ : Base → ℝ} {x : Base} (hx : θ x = 0) :
    twistedRuledCoordinates θ x = (![x 0,0],x 1) := by
  simp [twistedRuledCoordinates,hx]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
