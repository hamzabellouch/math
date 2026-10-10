import OAI.Analysis.KadisonKastler.ModularCyclicGroup
import OAI.Analysis.KadisonKastler.CharacterContinuity
import OAI.Analysis.KadisonKastler.L2KernelSwap

namespace OAI

/-! # The cyclic gauge as a field of scalar characters

Interchanging the time and spectral variables turns the cyclic modular
gauge into ordinary character multiplication in each spectral fiber.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

section CharacterField

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

include hl

theorem characterField_measurable (f : RegularCoreHilbert ℂ) :
    AEStronglyMeasurable (fun s => (regularCharacterUnitary (H := ℂ) (l s) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) μ :=
  ((continuous_regularCharacterUnitary f).stronglyMeasurable.comp_measurable hl).aestronglyMeasurable

theorem characterField_star_measurable (f : RegularCoreHilbert ℂ) :
    AEStronglyMeasurable (fun s => (star (regularCharacterUnitary (H := ℂ) (l s)) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) μ := by
  have he (s : X) : star (regularCharacterUnitary (H := ℂ) (l s)) =
      regularCharacterUnitary (H := ℂ) (-(l s)) :=
    regularGroup_star_eq (regularCharacterRepresentation (H := ℂ)) (l s)
  have he' : (fun s => (star (regularCharacterUnitary (H := ℂ) (l s)) :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      (fun s => (regularCharacterUnitary (H := ℂ) (-(l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) := by
    funext s
    exact congrArg (fun u : unitary (RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) =>
      (u : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) (he s)
  rw [he']
  exact ((continuous_regularCharacterUnitary f).stronglyMeasurable.comp_measurable hl.neg).aestronglyMeasurable

def characterField : unitary (Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) :=
  regularUnitaryField μ (fun s => regularCharacterUnitary (H := ℂ) (l s))
    (characterField_measurable μ l hl) (characterField_star_measurable μ l hl)

theorem characterField_apply_ae (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    (characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F =ᵐ[μ]
      fun s => (regularCharacterUnitary (H := ℂ) (l s) : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (F s) :=
  regularUnitaryField_apply_ae μ _ _ _ F

end CharacterField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

theorem cyclicGauge_tensor_rows (f : Lp ℂ 2 (volume : Measure ℝ))
    (v : ModularCyclicSpace M J Ω x) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ s ∂resolventVectorMeasure (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x,
      ((regularGauge (modularCyclicGroup J Ω hsep hcyc x)
        (modularCyclicGroup_continuous J Ω hsep hcyc x) :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)) (scalarLpTensor volume f v)) t s =
        modularSpectralPhase t s.val * f t * v s := by
  let U := modularCyclicGroup J Ω hsep hcyc x
  filter_upwards [regularGauge_apply_ae U (modularCyclicGroup_continuous J Ω hsep hcyc x)
    (scalarLpTensor volume f v), scalarLpTensor_apply_ae volume f v] with t ht hf
  have he := ht.trans (congrArg
    (U (Multiplicative.ofAdd t) : ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) hf)
  filter_upwards [modularCyclicGroup_apply_ae J Ω hsep hcyc x t (f t • v),
    Lp.coeFn_smul (f t) v] with s hs hv
  calc
    _ = ((U (Multiplicative.ofAdd t) : ModularCyclicSpace M J Ω x →L[ℂ]
        ModularCyclicSpace M J Ω x) (f t • v)) s :=
      congrArg (fun w : ModularCyclicSpace M J Ω x => w s) he
    _ = modularSpectralPhase t s.val * (f t • v) s := hs
    _ = _ := by rw [hv]; change _ * (f t * v s) = _; ring

theorem characterField_tensor_rows {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 μ) :
    ∀ᵐ s ∂μ, ∀ᵐ t ∂(volume : Measure ℝ),
      ((characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
        Lp (RegularCoreHilbert ℂ) 2 μ) (scalarLpTensor μ v f)) s t =
      regularCharacterScalar (l s) t * f t * v s := by
  filter_upwards [characterField_apply_ae μ l hl (scalarLpTensor μ v f),
    scalarLpTensor_apply_ae μ v f] with s ht hv
  have he := ht.trans (congrArg
    (regularCharacterUnitary (H := ℂ) (l s) : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) hv)
  filter_upwards [regularCharacterUnitary_apply_ae (l s) (v s • f), Lp.coeFn_smul (v s) f]
    with t ht hf
  calc
    _ = ((regularCharacterUnitary (H := ℂ) (l s) : RegularCoreHilbert ℂ →L[ℂ]
        RegularCoreHilbert ℂ) (v s • f)) t :=
      congrArg (fun w : RegularCoreHilbert ℂ => w t) he
    _ = regularCharacterScalar (l s) t • (v s • f) t := ht
    _ = _ := by rw [hf]; change _ * (v s * f t) = _; ring

theorem cyclicGauge_swap_tensor (f : Lp ℂ 2 (volume : Measure ℝ))
    (v : ModularCyclicSpace M J Ω x) :
    l2ScalarSwap volume (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      ((regularGauge (modularCyclicGroup J Ω hsep hcyc x)
        (modularCyclicGroup_continuous J Ω hsep hcyc x) :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)) (scalarLpTensor volume f v)) =
    (characterField (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint x)
      (fun s => resolventLogFrequency s.val)
      (resolventLogFrequency_measurable.comp measurable_subtype_coe) :
      Lp (RegularCoreHilbert ℂ) 2 (resolventVectorMeasure (graphResolvent M J Ω 1)
        (graphResolvent_positive J Ω 1).isSelfAdjoint x) →L[ℂ] _)
      (scalarLpTensor _ v f) := by
  let R := graphResolvent M J Ω 1
  let hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR x
  let U := modularCyclicGroup J Ω hsep hcyc x
  let hU := modularCyclicGroup_continuous J Ω hsep hcyc x
  let l : spectrum ℝ R → ℝ := fun s => resolventLogFrequency s.val
  have hl : Measurable l := resolventLogFrequency_measurable.comp measurable_subtype_coe
  let k : ℝ × spectrum ℝ R → ℂ := fun p => modularSpectralPhase p.1 p.2.val
  let F := (regularGauge U hU : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
    RegularCoreHilbert (ModularCyclicSpace M J Ω x)) (scalarLpTensor volume f v)
  let G := (characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
    Lp (RegularCoreHilbert ℂ) 2 μ) (scalarLpTensor μ v f)
  change l2ScalarSwap volume μ F = G
  apply l2ScalarSwap_of_kernel volume μ (fun t s => k (t, s) * f t * v s) F G
  · exact cyclicGauge_tensor_rows J Ω hsep hcyc x f v
  · have h := characterField_tensor_rows μ l hl f v
    filter_upwards [h] with s hs
    filter_upwards [hs] with t ht
    exact ht.trans (congrArg (fun z : ℂ => z * f t * v s)
      (modularSpectralPhase_eq_character s.val t).symm)
  · intro f' v'
    apply integrable_bounded_L2_kernel volume μ k _ (fun p => (modularSpectralPhase_norm _ _).le) f f' v v'
    change Measurable (fun p : ℝ × spectrum ℝ R =>
      Complex.exp (Complex.I * ((p.1 : ℂ) * (resolventLogFrequency p.2.val : ℂ))))
    exact Complex.continuous_exp.measurable.comp
      (measurable_const.mul ((Complex.continuous_ofReal.measurable.comp measurable_fst).mul
        (Complex.continuous_ofReal.measurable.comp
          (resolventLogFrequency_measurable.comp (measurable_subtype_coe.comp measurable_snd)))))

end

end KadisonKastler

end OAI
