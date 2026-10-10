import OAI.Geometry.SurfaceImmersion.Geometry.TriangularSurfaceImmersion
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCutoffBounds

namespace OAI

/-! The third component of a compactly supported cancellation of the
standard polynomial pair, and its exact vertical derivative. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def cancellationHeight (χ : ℝ → ℝ) (R : ℝ) (x : Base) : ℝ :=
  (x 1)^3-3*x 1+4*χ (x 0)*χ (x 1/R)*x 1

lemma cancellationHeight_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (R : ℝ) :
    ContDiff ℝ ∞ (cancellationHeight χ R) := by
  have h0 : ContDiff ℝ ∞ (fun x : Base => x 0) :=
    (ContinuousLinearMap.proj (0 : Fin 2) : Base →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ ∞ (fun x : Base => x 1) :=
    (ContinuousLinearMap.proj (1 : Fin 2) : Base →L[ℝ] ℝ).contDiff
  exact ((h1.pow 3).sub (contDiff_const.mul h1)).add
    (((contDiff_const.mul (hχ.comp h0)).mul (hχ.comp (h1.div_const R))).mul h1)

lemma cancellationHeight_slice_hasDerivAt {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (R c y : ℝ) :
    HasDerivAt (fun t => cancellationHeight χ R ![c,t])
      (3*y^2-3+4*χ c*(χ (y/R)+(y/R)*deriv χ (y/R))) y := by
  have hχy : HasDerivAt (fun t => χ (t/R)) (deriv χ (y/R) / R) y := by
    convert ((hχ.differentiable (by simp) (y/R)).hasDerivAt).comp y
      ((hasDerivAt_id y).div_const R) using 1
    · funext t
      simp only [Function.comp_apply,id_eq,div_eq_mul_inv]
    · simp only [div_eq_mul_inv]
      ring
  have hp := (((hasDerivAt_id y).pow 3).sub ((hasDerivAt_id y).const_mul 3)).add
    ((hχy.const_mul (4*χ c)).mul (hasDerivAt_id y))
  convert hp using 1
  · funext t
    simp only [cancellationHeight,Matrix.cons_val_one,Matrix.cons_val_zero]
    rfl
  · simp only [id_eq]
    ring

lemma cancellationHeight_vertical {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : χ 0 = 1) (R : ℝ) {x : Base} (hx : x 0 = 0) :
    fderiv ℝ (cancellationHeight χ R) x ![0,1] =
      3*(x 1)^2-3+4*(χ (x 1/R)+(x 1/R)*deriv χ (x 1/R)) := by
  let path : ℝ → Base := fun t => ![x 0,t]
  have hpath : HasDerivAt path (![0,1] : Base) (x 1) := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_const (x 1) (x 0)
    · exact hasDerivAt_id (x 1)
  have hvalue : path (x 1) = x := by
    ext i
    fin_cases i <;> rfl
  have hder := ((cancellationHeight_smooth hχ R).differentiable (by simp)
    (path (x 1))).hasFDerivAt.comp_hasDerivAt (x 1) hpath
  rw [hvalue] at hder
  have hs := cancellationHeight_slice_hasDerivAt hχ R (x 0) (x 1)
  have hh := hder.unique hs
  simpa only [hx,hχ0,mul_one] using hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
