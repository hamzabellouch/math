import OAI.Geometry.SurfaceImmersion.Whitney.SlowCollarCutoff
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets

namespace OAI

/-! The exact derivative of a collar whose transverse vector follows a
 prescribed smooth homotopy; only u and u times the cutoff derivative
 enter as perturbation parameters. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def homotopyCollar (c : ℝ → W) (V : ℝ × ℝ → W) (χ : ℝ → ℝ) (x : Base) : W :=
  c (x 1) + x 0 • V (χ (x 0),x 1)

def homotopyCollarJet (c : ℝ → W) (V : ℝ × ℝ → W) (s t u w : ℝ) : Base →L[ℝ] W :=
  (ContinuousLinearMap.proj 1).smulRight (deriv c t) +
    (ContinuousLinearMap.proj 0).smulRight (V (s,t)) +
    (ContinuousLinearMap.proj 0).smulRight (w • fderiv ℝ V (s,t) (1,0)) +
    (ContinuousLinearMap.proj 1).smulRight (u • fderiv ℝ V (s,t) (0,1))

lemma homotopyCollar_smooth {c : ℝ → W} {V : ℝ × ℝ → W} {χ : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (homotopyCollar c V χ) := by
  exact (hc.comp (contDiff_apply ℝ ℝ 1)).add
    ((contDiff_apply ℝ ℝ 0).smul (hV.comp
      ((hχ.comp (contDiff_apply ℝ ℝ 0)).prodMk (contDiff_apply ℝ ℝ 1))))

lemma homotopyCollarJet_continuous {c : ℝ → W} {V : ℝ × ℝ → W}
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) :
    Continuous (fun z : (ℝ × ℝ) × Base => homotopyCollarJet c V z.1.1 z.1.2 (z.2 0) (z.2 1)) := by
  have hdc' : ContDiff ℝ ∞ (deriv c) := hc.deriv'
  have hdc : Continuous (deriv c) := hdc'.continuous
  have hdV : Continuous (fderiv ℝ V) := hV.continuous_fderiv (by simp)
  unfold homotopyCollarJet
  fun_prop

lemma homotopyCollar_fderiv {c : ℝ → W} {V : ℝ × ℝ → W} {χ : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) (hχ : ContDiff ℝ ∞ χ) (x : Base) :
    fderiv ℝ (homotopyCollar c V χ) x =
      homotopyCollarJet c V (χ (x 0)) (x 1) (x 0) (x 0*deriv χ (x 0)) := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have hC := ((hc.differentiable (by simp) _).hasDerivAt.hasFDerivAt).comp x h1
  have hX := ((hχ.differentiable (by simp) _).hasDerivAt.hasFDerivAt).comp x h0
  have hp := hX.prodMk h1
  have hvec := ((hV.differentiable (by simp) _).hasFDerivAt).comp x hp
  have hd := hC.add (h0.smul hvec)
  change HasFDerivAt (homotopyCollar c V χ) _ x at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  have hv : (v 0*deriv χ (x 0),v 1) =
      (v 0*deriv χ (x 0)) • ((1,0) : ℝ × ℝ) + v 1 • ((0,1) : ℝ × ℝ) := by
    ext <;> simp
  simp only [homotopyCollarJet, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, smul_eq_mul]
  change v 1 • deriv c (x 1) +
    (x 0 • fderiv ℝ V (χ (x 0),x 1) (v 0 * deriv χ (x 0),v 1) +
      v 0 • V (χ (x 0),x 1)) =
    v 1 • deriv c (x 1) + v 0 • V (χ (x 0),x 1) +
      v 0 • ((x 0 * deriv χ (x 0)) • fderiv ℝ V (χ (x 0),x 1) (1,0)) +
      v 1 • (x 0 • fderiv ℝ V (χ (x 0),x 1) (0,1))
  rw [hv,map_add,map_smul,map_smul]
  module

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
