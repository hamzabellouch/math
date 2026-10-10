import OAI.Geometry.Immersion.ClosedSurface.DoubleModes
import OAI.Geometry.Immersion.ClosedSurface.ComplexPullback

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.QuadraticMean (displacement realMode)
open ClosedSurfaceR4.WeightedEstimates

def phaseCancelAmplitude {n : ℕ} (τ : ℝ) (F : RField n)
    (e : Base → Base) (A : Base → ComplexTensor) (q : ℕ) : Field n :=
  modeApprox τ (fun p => complexify (F (e p))) (fun _ => 0)
    (fun p => -coordinateTarget e A p) q

def phaseCanceller {n : ℕ} (τ : ℝ) (F : RField n) (χ e : Base → Base)
    (A : Base → ComplexTensor) (q : ℕ) : RField n :=
  realOsc τ (phaseCancelAmplitude τ F e A q) ∘ χ

lemma contDiffOn_phaseCanceller {n : ℕ} {U V : Set Base}
    {F : RField n} {χ e : Base → Base} {A : Base → ComplexTensor}
    (h : ModeDomain (fun p => complexify (F (e p))) V)
    (hχ : ContDiffOn ℝ ∞ χ U) (hχV : Set.MapsTo χ U V)
    (he : ContDiffOn ℝ ∞ e V) (heU : Set.MapsTo e V U)
    (hA : ContDiffOn ℝ ∞ A U) (τ : ℝ) (q : ℕ) :
    ContDiffOn ℝ ∞ (phaseCanceller τ F χ e A q) U := by
  apply (contDiffOn_realOsc (contDiffOn_modeApprox τ h contDiffOn_const
    (contDiffOn_coordinateTarget h.isOpen hA he heU).neg q) τ).comp hχ hχV

lemma realLinearizedTensor_congr_left {n : ℕ} {F G X : RField n} {p : Base}
    (h : F =ᶠ[nhds p] G) : realLinearizedTensor F X p = realLinearizedTensor G X p := by
  ext i
  simp only [realLinearizedTensor_apply, realLinearized, coordDeriv, h.fderiv_eq]



theorem phaseCanceller_residual {n : ℕ} {F : RField n} {χ e : Base → Base}
    {A : Base → ComplexTensor} {p : Base} {τ : ℝ} {q : ℕ}
    (hF : DifferentiableAt ℝ F (e (χ p))) (he : DifferentiableAt ℝ e (χ p))
    (hχ : DifferentiableAt ℝ χ p) (hinv : e ∘ χ =ᶠ[nhds p] id)
    (hZ : DifferentiableAt ℝ (phaseCancelAmplitude τ F e A q) (χ p)) :
    realLinearizedTensor F (phaseCanceller τ F χ e A q) p +
      displacement τ (fun p => (χ p).1) A p =
    pullbackField χ p
      (realOsc τ (SmallModes.residual τ (fun p => complexify (F (e p)))
        (fun p => -coordinateTarget e A p) (phaseCancelAmplitude τ F e A q)) (χ p)) := by
  have hcomp : (F ∘ e) ∘ χ =ᶠ[nhds p] F := hinv.mono (fun z hz => congrArg F hz)
  have hO : DifferentiableAt ℝ (realOsc τ (phaseCancelAmplitude τ F e A q)) (χ p) := by
    exact (QuadraticMean.realPartCLM n).differentiableAt.comp (χ p)
      ((unitMode_hasFDerivAt τ (χ p)).differentiableAt.smul hZ)
  have hres := realLinearized_residual (hF.comp (χ p) he) hZ τ
    (fun p => -coordinateTarget e A p)
  have htarget : pullbackField χ p (realOsc τ (fun p => -coordinateTarget e A p) (χ p)) =
      -displacement τ (fun p => (χ p).1) A p := by
    rw [realOsc_neg, map_neg, realOsc_eq_displacement]
    change -(pullbackField χ p (realMode ((χ p).1 / τ)
      (complexPullbackField e (χ p) (A (e (χ p)))))) = -realMode ((χ p).1 / τ) (A p)
    have hpoint : e (χ p) = p := hinv.eq_of_nhds
    rw [hpoint]
    exact congrArg Neg.neg (oscillating_pullback_inverse hχ he hinv (A p) _)
  rw [← realLinearizedTensor_congr_left (X := phaseCanceller τ F χ e A q) hcomp]
  change realLinearizedTensor ((F ∘ e) ∘ χ)
    (realOsc τ (phaseCancelAmplitude τ F e A q) ∘ χ) p + _ = _
  rw [realLinearizedTensor_comp (hF.comp (χ p) he) hO hχ]
  simp only [Function.comp_def] at hres
  rw [← hres, map_sub, htarget, sub_neg_eq_add]
  rfl

end ClosedSurfaceR4.RealModes

end

end OAI
