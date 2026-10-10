import OAI.Geometry.RCD.Sobolev.LocalHessianAction

namespace OAI

/-! # Integrability and the exact integral of the Hessian action -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem localHessianAction_integrable (f v u fv fu vu : SobolevSpace μ hQ) :
    Integrable (localHessianAction μ hQ f v u fv fu vu) μ := by
  simpa only [localHessianAction,Pi.add_apply,Pi.sub_apply] using!
    (((localGamma_memL1 μ hQ v fu).add (localGamma_memL1 μ hQ u fv)).sub
      (localGamma_memL1 μ hQ f vu)).div_const 2

omit [ProperSpace X] in
theorem integral_localHessianAction (f v u fv fu vu : SobolevSpace μ hQ) :
    (∫ x, localHessianAction μ hQ f v u fv fu vu x ∂μ) =
      (energyForm μ hQ v fu+energyForm μ hQ u fv-energyForm μ hQ f vu)/2 := by
  have hsum : Integrable (fun x => localGamma μ hQ v fu x+localGamma μ hQ u fv x) μ := by
    simpa only [Pi.add_apply] using! (localGamma_memL1 μ hQ v fu).add (localGamma_memL1 μ hQ u fv)
  simp only [localHessianAction]
  rw [integral_div,integral_sub hsum
    (localGamma_memL1 μ hQ f vu),
    integral_add (localGamma_memL1 μ hQ v fu) (localGamma_memL1 μ hQ u fv),
    integral_localGamma_eq_energyForm,integral_localGamma_eq_energyForm,integral_localGamma_eq_energyForm]

omit [ProperSpace X] in
/-- The pointwise three-term action agrees with the continuous Hessian
functional on the constructed dense test core. -/
theorem LocalHessianPairing.integral_action_core {Ω : Set X} {f a : SobolevSpace μ hQ}
    (G : LocalHessianPairing μ hQ Ω f a) (φ : G.core) :
    (∫ x, localHessianAction μ hQ f a φ.val.val G.mixed
      (G.gammaF φ).val (G.gammaA φ).val x ∂μ) = G.hessian φ.val := by
  rw [integral_localHessianAction]
  have h := G.koszul φ
  linarith only [h]

end RegularPointCoordinates

end

end OAI
