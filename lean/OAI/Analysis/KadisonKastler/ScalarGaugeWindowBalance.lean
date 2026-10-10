import OAI.Analysis.KadisonKastler.CoreTraceScalarGauge
import OAI.Analysis.KadisonKastler.CyclicGaugeSwap
import OAI.Analysis.KadisonKastler.DirectIntegralUnitary

namespace OAI

/-! # Scalar-field and gauge lifting of the finite-window trace identity -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyWindow_tensor (a b : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularFrequencyWindow a b (scalarLpTensor volume f v) =
      scalarLpTensor volume (regularFrequencyWindow a b f) v := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularFrequencyWindow a b (scalarLpTensor volume f v)) :
    RegularCoreHilbert H) = 𝓕 (scalarLpTensor volume (regularFrequencyWindow a b f) v)
  rw [fourier_frequencyWindow, fourier_scalarLpTensor,
    fourier_scalarLpTensor, fourier_frequencyWindow]
  exact regularIndicatorProjection_tensor (Set.Ioc a b) measurableSet_Ioc (𝓕 f) v

theorem l2ScalarSwap_frequencyWindow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (a b : ℝ) (F : RegularCoreHilbert (Lp ℂ 2 μ)) :
    l2ScalarSwap volume μ (regularFrequencyWindow a b F) =
      (regularFrequencyWindow (H := ℂ) a b).compLp (l2ScalarSwap volume μ F) := by
  apply l2ScalarSwap_intertwines_of_tensor volume μ
    (regularFrequencyWindow a b) ((regularFrequencyWindow (H := ℂ) a b).compLpL 2 μ)
  intro f v
  rw [regularFrequencyWindow_tensor, l2ScalarSwap_tensor]
  exact (compLp_scalarLpTensor μ (regularFrequencyWindow (H := ℂ) a b) v f).symm

theorem characterField_window_balance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (f : RegularCoreHilbert ℂ) (v w : Lp ℂ 2 μ)
    (hbalance : ∀ᵐ s ∂μ,
      v s • regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (l s)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      w s • (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (l s) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f))) :
    let E := Lp (RegularCoreHilbert ℂ) 2 μ
    let C : E →L[ℂ] E := characterField μ l hl
    let Cs : E →L[ℂ] E := star (characterField μ l hl)
    let P := regularFrequencyWindow (H := ℂ) 0 1
    P.compLp (Cs (scalarLpTensor μ v f)) =
      Cs (P.compLp (C (scalarLpTensor μ w f))) := by
  let C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
    characterField μ l hl
  let Cs : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
    star (characterField μ l hl)
  let P := regularFrequencyWindow (H := ℂ) 0 1
  have hstar (F : Lp (RegularCoreHilbert ℂ) 2 μ) :=
    regularUnitaryField_star_apply_ae μ (fun s => regularCharacterUnitary (H := ℂ) (l s))
      (characterField_measurable μ l hl) (characterField_star_measurable μ l hl) F
  apply Lp.ext
  filter_upwards [P.coeFn_compLp (Cs (scalarLpTensor μ v f)),
    hstar (scalarLpTensor μ v f), scalarLpTensor_apply_ae μ v f,
    hstar (P.compLp (C (scalarLpTensor μ w f))),
    P.coeFn_compLp (C (scalarLpTensor μ w f)),
    characterField_apply_ae μ l hl (scalarLpTensor μ w f),
    scalarLpTensor_apply_ae μ w f, hbalance]
    with s hp hcl hv hcr hpr hc hw hb
  change (Cs (scalarLpTensor μ v f)) s = _ at hcl
  change (Cs (P.compLp (C (scalarLpTensor μ w f)))) s = _ at hcr
  change (P.compLp (Cs (scalarLpTensor μ v f))) s =
    (Cs (P.compLp (C (scalarLpTensor μ w f)))) s
  rw [hp, hcl, hv, hcr, hpr, hc, hw]
  simpa only [map_smul] using hb


theorem scalarGaugeWindowBalance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (G : unitary (RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ)))
    (hG : ∀ F, l2ScalarSwap volume μ ((G :
      RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ)) F) =
      (characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
        Lp (RegularCoreHilbert ℂ) 2 μ) (l2ScalarSwap volume μ F))
    (f : RegularCoreHilbert ℂ) (v w : Lp ℂ 2 μ)
    (hbalance : ∀ᵐ s ∂μ,
      v s • regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (l s)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      w s • (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (l s) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f))) :
    regularFrequencyWindow 0 1
      ((star G : RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ))
        (scalarLpTensor volume f v)) =
      (star G : RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ))
        (regularFrequencyWindow 0 1
          ((G : RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ))
            (scalarLpTensor volume f w))) := by
  let E := RegularCoreHilbert (Lp ℂ 2 μ)
  let F := Lp (RegularCoreHilbert ℂ) 2 μ
  let S := l2ScalarSwap (volume : Measure ℝ) μ
  let C : F →L[ℂ] F := characterField μ l hl
  let Cs : F →L[ℂ] F := star (characterField μ l hl)
  let P := regularFrequencyWindow (H := ℂ) 0 1
  have hs (u : E) : S ((star G : E →L[ℂ] E) u) = Cs (S u) := by
    exact intertwines_unitary_star S.toContinuousLinearEquiv.toContinuousLinearMap
      G (characterField μ l hl) hG u
  have hleft : S (regularFrequencyWindow 0 1
      ((star G : E →L[ℂ] E) (scalarLpTensor volume f v))) =
      P.compLp (Cs (scalarLpTensor μ v f)) := by
    calc
      _ = P.compLp (S ((star G : E →L[ℂ] E) (scalarLpTensor volume f v))) :=
        l2ScalarSwap_frequencyWindow μ 0 1 _
      _ = P.compLp (Cs (S (scalarLpTensor volume f v))) := congrArg P.compLp (hs _)
      _ = _ := congrArg (fun z => P.compLp (Cs z)) (l2ScalarSwap_tensor volume μ f v)
  have hright : S ((star G : E →L[ℂ] E)
      (regularFrequencyWindow 0 1 ((G : E →L[ℂ] E) (scalarLpTensor volume f w)))) =
      Cs (P.compLp (C (scalarLpTensor μ w f))) := by
    calc
      _ = Cs (S (regularFrequencyWindow 0 1
          ((G : E →L[ℂ] E) (scalarLpTensor volume f w)))) := hs _
      _ = Cs (P.compLp (S ((G : E →L[ℂ] E) (scalarLpTensor volume f w)))) :=
        congrArg Cs (l2ScalarSwap_frequencyWindow μ 0 1 _)
      _ = Cs (P.compLp (C (S (scalarLpTensor volume f w)))) :=
        congrArg (fun z => Cs (P.compLp z)) (hG _)
      _ = _ := congrArg (fun z => Cs (P.compLp (C z))) (l2ScalarSwap_tensor volume μ f w)
  apply S.injective
  exact hleft.trans ((characterField_window_balance μ l hl f v w hbalance).trans hright.symm)

end

end KadisonKastler

end OAI
