import OAI.Analysis.KadisonKastler.L2Intertwining
import OAI.Analysis.KadisonKastler.CyclicGaugeSwap
import OAI.Analysis.KadisonKastler.ShiftedFrequencyFields
import OAI.Analysis.KadisonKastler.DirectIntegralUnitary

namespace OAI

/-! # Frequency projections after the scalar variable swap -/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem l2ScalarSwap_frequency (μ : Measure X) (a : ℝ)
    (F : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ)) :
    l2ScalarSwap volume μ (regularFrequencyProjection a F) =
      (regularFrequencyProjection (H := ℂ) a).compLp (l2ScalarSwap volume μ F) := by
  apply l2ScalarSwap_intertwines_of_tensor (volume : Measure ℝ) μ
    (regularFrequencyProjection a) ((regularFrequencyProjection (H := ℂ) a).compLpL 2 μ)
  intro f v
  have ht : regularFrequencyProjection a (scalarLpTensor volume f v) =
      scalarLpTensor volume (regularFrequencyProjection a f) v :=
    (compLp_regularFrequencyProjection (ContinuousLinearMap.toSpanSingleton ℂ v) a f).symm
  calc
    _ = l2ScalarSwap volume μ (scalarLpTensor volume (regularFrequencyProjection a f) v) :=
      congrArg (l2ScalarSwap volume μ) ht
    _ = scalarLpTensor μ v (regularFrequencyProjection a f) := l2ScalarSwap_tensor volume μ _ _
    _ = _ := (compLp_scalarLpTensor μ (regularFrequencyProjection (H := ℂ) a) v f).symm

theorem characterField_frequency_conjugate (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (a : ℝ) (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    (star (characterField μ l hl) : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ)
      ((regularFrequencyProjection (H := ℂ) a).compLp
        ((characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F)) =
      shiftedFrequencyField μ l hl a F := by
  let C := characterField μ l hl
  let P := regularFrequencyProjection (H := ℂ) a
  have hs := regularUnitaryField_star_apply_ae μ (fun s => regularCharacterUnitary (H := ℂ) (l s))
    (characterField_measurable μ l hl) (characterField_star_measurable μ l hl)
    (P.compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F))
  change (star C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ)
    (P.compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F)) =ᵐ[μ] _ at hs
  apply Lp.ext
  filter_upwards [hs, P.coeFn_compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
      Lp (RegularCoreHilbert ℂ) 2 μ) F), characterField_apply_ae μ l hl F,
    shiftedFrequencyField_apply_ae μ l hl a F] with s hs hp hc ht
  calc
    _ = (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        ((P.compLp ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F)) s) := hs
    _ = (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (P ((C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ) F s)) :=
      congrArg (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) hp
    _ = (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (P ((regularCharacterUnitary (H := ℂ) (l s) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (F s))) :=
      congrArg (fun w => (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (P w)) hc
    _ = regularFrequencyProjection (a - l s) (F s) :=
      congrArg (fun T : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ => T (F s))
        (character_frequency_cut a (l s))
    _ = _ := ht.symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

theorem cyclicGauge_frequency_swap (a : ℝ) (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    l2ScalarSwap volume (modularCyclicMeasure (M := M) J Ω x)
      ((star (modularCyclicGauge J Ω hsep hcyc x) : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ] RegularCoreHilbert (ModularCyclicSpace M J Ω x))
        (regularFrequencyProjection a ((modularCyclicGauge J Ω hsep hcyc x : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ] RegularCoreHilbert (ModularCyclicSpace M J Ω x)) F))) =
      shiftedFrequencyField (modularCyclicMeasure (M := M) J Ω x) (fun s => resolventLogFrequency s.val)
        (resolventLogFrequency_measurable.comp measurable_subtype_coe) a
        (l2ScalarSwap volume (modularCyclicMeasure (M := M) J Ω x) F) := by
  let μ := modularCyclicMeasure (M := M) J Ω x
  let S := l2ScalarSwap (volume : Measure ℝ) μ
  let G : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
      RegularCoreHilbert (ModularCyclicSpace M J Ω x) := modularCyclicGauge J Ω hsep hcyc x
  let Gs : RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
      RegularCoreHilbert (ModularCyclicSpace M J Ω x) := star (modularCyclicGauge J Ω hsep hcyc x)
  let C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
    modularCharacterField (M := M) J Ω x
  let Cs : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
    star (modularCharacterField (M := M) J Ω x)
  let P := regularFrequencyProjection (H := ℂ) a
  change S (Gs (regularFrequencyProjection a (G F))) = _
  calc
    _ = Cs (S (regularFrequencyProjection a (G F))) :=
      cyclicGauge_star_swap J Ω hsep hcyc x _
    _ = Cs (P.compLp (S (G F))) := congrArg Cs (l2ScalarSwap_frequency μ a (G F))
    _ = Cs (P.compLp (C (S F))) :=
      congrArg (fun w => Cs (P.compLp w)) (cyclicGauge_swap J Ω hsep hcyc x F)
    _ = _ := characterField_frequency_conjugate μ _ _ a (S F)

end

end KadisonKastler

end OAI
