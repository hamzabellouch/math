import OAI.Analysis.KadisonKastler.CyclicCutField
import OAI.Analysis.KadisonKastler.FourierShiftedFields
import OAI.Analysis.KadisonKastler.L2SwapIntertwining

namespace OAI

/-! # Interchanging the variables of the modular cut field -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

section Scalar

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

theorem fourierShiftedField_tensor_rows (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 μ) :
    ∀ᵐ s ∂μ, ∀ᵐ ξ ∂(volume : Measure ℝ),
      (fourierShiftedField μ l hl a (scalarLpTensor μ v f)) s ξ =
        (if a < l s + 2 * Real.pi * ξ then (1 : ℂ) else 0) * f ξ * v s := by
  filter_upwards [fourierShiftedField_apply_ae μ l hl a (scalarLpTensor μ v f),
    scalarLpTensor_apply_ae μ v f] with s hF hv
  have he := hF.trans (congrArg (scalarFourierCut (a - l s)) hv)
  filter_upwards [scalarFourierCut_apply_ae (a - l s) (v s • f), Lp.coeFn_smul (v s) f]
    with ξ hc hf
  have hcond : ξ ∈ Set.Ioi ((a - l s) / (2 * Real.pi)) ↔ a < l s + 2 * Real.pi * ξ := by
    change (a - l s) / (2 * Real.pi) < ξ ↔ _
    rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
    constructor <;> intro h <;> nlinarith
  have hind : (Set.Ioi ((a - l s) / (2 * Real.pi))).indicator (v s • f) ξ =
      (if a < l s + 2 * Real.pi * ξ then (1 : ℂ) else 0) * f ξ * v s := by
    by_cases h : a < l s + 2 * Real.pi * ξ
    · rw [Set.indicator_of_mem (hcond.mpr h), hf, ite_eq_left h]
      change v s * f ξ = _
      ring
    · rw [Set.indicator_of_notMem (mt hcond.mp h), ite_eq_right h]
      simp
  calc
    _ = (scalarFourierCut (a - l s) (v s • f)) ξ :=
      congrArg (fun w : RegularCoreHilbert ℂ => w ξ) he
    _ = _ := hc.trans hind

end Scalar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

include hsep hcyc

theorem cyclicCutField_swap_tensor (a : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : ModularCyclicSpace M J Ω x) :
    l2ScalarSwap volume
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (modularCyclicCutField M J Ω x a (scalarLpTensor volume f v)) =
    fourierShiftedField
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a (scalarLpTensor _ v f) := by
  let R := graphResolvent M J Ω 1
  let hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR x
  let l : spectrum ℝ R → ℝ := fun s => resolventLogFrequency s.val
  have hl : Measurable l := resolventLogFrequency_measurable.comp measurable_subtype_coe
  let k : ℝ × spectrum ℝ R → ℂ := fun p => if a < l p.2 + 2 * Real.pi * p.1 then 1 else 0
  apply l2ScalarSwap_of_kernel volume μ (fun ξ s => k (ξ, s) * f ξ * v s)
  · exact cyclicCutField_tensor_rows J Ω hsep hcyc x a f v
  · exact fourierShiftedField_tensor_rows μ l hl a f v
  · intro f' v'
    apply integrable_bounded_L2_kernel volume μ k _ _ f f' v v'
    · exact Measurable.ite
        (measurableSet_lt measurable_const
          ((hl.comp measurable_snd).add (measurable_const.mul measurable_fst)))
        measurable_const measurable_const
    · intro p
      dsimp [k]
      split <;> simp

theorem cyclicCutField_swap (a : ℝ) (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    l2ScalarSwap volume
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (modularCyclicCutField M J Ω x a F) =
    fourierShiftedField
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a
      (l2ScalarSwap volume
        (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x) F) := by
  exact l2ScalarSwap_intertwines_of_tensor (volume : Measure ℝ)
    (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
    (modularCyclicCutField M J Ω x a)
    (fourierShiftedField
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) a)
    (cyclicCutField_swap_tensor J Ω hsep hcyc x a) F

end

end KadisonKastler

end OAI
