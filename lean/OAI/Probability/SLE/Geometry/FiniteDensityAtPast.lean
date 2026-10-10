import OAI.Probability.SLE.Gauge.RandomPassageBounds

namespace OAI

/-! The finite tilted law on a stopped-past event is the integral of its
conditional density there. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

theorem normalizedDensity_measure_at_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Z M : Ω → ℝ) (hZi : Integrable Z P) (hZn : 0 ≤ᵐ[P] Z)
    (hM : M =ᵐ[P] P[Z | m]) (a : ℝ) (ha : 0 < a)
    (E : Set Ω) (hE : MeasurableSet[m] E) :
    P.withDensity (fun ω => ENNReal.ofReal (Z ω / a)) E =
      ∫⁻ ω in E, ENNReal.ofReal (M ω / a) ∂P := by
  let : MeasurableSpace Ω := mΩ
  have hcond := condLExp_ofReal m hZi hZn
  have he : (∫⁻ ω in E, ENNReal.ofReal (M ω) ∂P) =
      ∫⁻ ω in E, ENNReal.ofReal (Z ω) ∂P := by
    calc
      _ = ∫⁻ ω in E, P⁻[(fun ω => ENNReal.ofReal (Z ω)) | m] ω ∂P := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hM, ae_restrict_of_ae hcond] with ω hMω hcω
        rw [hcω, ← hMω]
      _ = _ := setLIntegral_condLExp hm P _ hE
  rw [setLIntegral_eq_mul_normalizedDensity P Z ha (hm E hE),
    setLIntegral_eq_mul_normalizedDensity P M ha (hm E hE)] at he
  have he' :
      P.withDensity (fun ω => ENNReal.ofReal (M ω / a)) E * ENNReal.ofReal a =
      P.withDensity (fun ω => ENNReal.ofReal (Z ω / a)) E * ENNReal.ofReal a :=
    (mul_comm _ _).trans (he.trans (mul_comm _ _))
  have hcancel := (ENNReal.mul_left_inj (ENNReal.ofReal_ne_zero_iff.mpr ha)
    ENNReal.ofReal_ne_top).mp he'
  rw [withDensity_apply _ (hm E hE)] at hcancel
  exact hcancel.symm

end SLEExactGauge

end

end OAI
