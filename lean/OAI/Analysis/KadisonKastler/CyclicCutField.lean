import OAI.Analysis.KadisonKastler.ModularCyclicCuts
import OAI.Analysis.KadisonKastler.L2KernelSwap

namespace OAI

/-! # The explicit scalar kernel of the modular cut field -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

def modularCyclicCutField (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) (a : ℝ) :
    RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
      RegularCoreHilbert (ModularCyclicSpace M J Ω x) :=
  regularFieldOperator volume (fun ξ => modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ))
    (modularCyclicCut_measurable J Ω x a) 1
    (Eventually.of_forall fun _ => modularCyclicCut_contracts J Ω x _)

theorem modularCyclicCutField_apply_ae (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) (a : ℝ)
    (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    modularCyclicCutField M J Ω x a F =ᵐ[volume]
      fun ξ => modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ) (F ξ) :=
  regularFieldOperator_represents volume _ _ _ _ F

omit [TopologicalSpace.SeparableSpace H] in
theorem modularCyclicCut_apply_ae (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) (a : ℝ)
    (v : ModularCyclicSpace M J Ω x) :
    modularCyclicCut M J Ω x a v =ᵐ[
      resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x]
      fun s => resolventCutIndicator (graphResolvent M J Ω 1) (modularCutThreshold a) s * v s :=
  resolventScalarMultiplier_apply_ae _ _ x _ (resolventCutIndicator_measurable _ _) 1
    (resolventCutIndicator_bound _ _) v

theorem cyclicCutField_tensor_rows (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : ModularCyclicSpace M J Ω x) :
    ∀ᵐ ξ ∂(volume : Measure ℝ), ∀ᵐ s ∂resolventVectorMeasure (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x,
      (modularCyclicCutField M J Ω x a (scalarLpTensor volume f v)) ξ s =
      (if a < resolventLogFrequency s.val + 2 * Real.pi * ξ then (1 : ℂ) else 0) * f ξ * v s := by
  filter_upwards [modularCyclicCutField_apply_ae J Ω x a (scalarLpTensor volume f v),
    scalarLpTensor_apply_ae volume f v] with ξ hF hf
  have he := hF.trans (congrArg (modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ)) hf)
  filter_upwards [modularCyclicCut_apply_ae J Ω x (a - 2 * Real.pi * ξ) (f ξ • v),
    Lp.coeFn_smul (f ξ) v, graphResolventVectorMeasure_interior J Ω hsep hcyc x] with s hs hv hint
  have hcond : s.val < modularCutThreshold (a - 2 * Real.pi * ξ) ↔
      a < resolventLogFrequency s.val + 2 * Real.pi * ξ := by
    rw [lt_modularCutThreshold_iff hint.1 hint.2]
    constructor <;> intro h <;> linarith
  have hind : resolventCutIndicator (graphResolvent M J Ω 1)
      (modularCutThreshold (a - 2 * Real.pi * ξ)) s =
      if a < resolventLogFrequency s.val + 2 * Real.pi * ξ then (1 : ℂ) else 0 := by
    change (if s.val < modularCutThreshold (a - 2 * Real.pi * ξ) then (1 : ℂ) else 0) = _
    simp only [hcond]
  calc
    _ = (modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ) (f ξ • v)) s :=
      congrArg (fun w : ModularCyclicSpace M J Ω x => w s) he
    _ = _ := by rw [hs, hv, hind]; change _ * (f ξ * v s) = _; ring

end

end KadisonKastler

end OAI
