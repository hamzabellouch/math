import OAI.Analysis.CircleDomains.Topology.CircleChainRule
import OAI.Analysis.CircleDomains.Sobolev.CovectorMetric

namespace OAI

/-!
# Conformal invariance of the actual circle-coordinate energy

The chain rule identifies the pullback field with the intrinsic
circle differential. Thus the change-of-variables formula controls
the actual composed coordinate, without a chosen global real lift.
-/

open Set Filter Matrix MeasureTheory

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem integral_circleEnergy_change_variables
    {s U : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hU : IsOpen U)
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf : ∀ x ∈ s, HasFDerivAt f (A x) x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, (A x).det ≠ 0) (hmap : MapsTo f s U)
    (u : (ℝ × ℝ) → UnitAddCircle) (hu : SmoothCircleOn u U)
    (g : (ℝ × ℝ) → PlanarMetric) (c : (ℝ × ℝ) → ℝ)
    (hc : ∀ x ∈ s, 0 < c x)
    (hg : ∀ x ∈ s, g x = c x • ((planeDerivativeMatrix (A x))ᵀ * planeDerivativeMatrix (A x))) :
    (∫ y in f '' s, fieldEnergy (circleGradient u) (fun _ => 1) y) =
      ∫ x in s, fieldEnergy (circleGradient (u ∘ f)) g x := by
  have heq := integral_covectorEnergy_change_variables hs f A
    (fun x hx => (hf x hx).hasFDerivWithinAt) hinj hdet
    (fun y => ![(circleGradient u y).1, (circleGradient u y).2]) (fun _ => 1)
    (fun _ _ => Matrix.PosDef.one) c hc
  refine heq.trans ?_
  apply setIntegral_congr_fun hs
  intro x hx
  have hvec := circleGradient_comp_vector hU hu (hf x hx).differentiableAt (hmap hx)
  rw [(hf x hx).fderiv] at hvec
  simp only [mul_one]
  rw [← hg x hx, ← hvec]
  rfl

end CircleDomainRigidity.FiniteTransfer

end

end OAI
