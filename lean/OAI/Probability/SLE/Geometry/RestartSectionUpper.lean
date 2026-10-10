import OAI.Probability.SLE.Geometry.RestartWeightedKernel

namespace OAI

/-! Upper bounds from measurable random sections of the independent fresh
driver law. The past state is allowed to vary without countable certificates. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

theorem restart_event_section_upper_bound
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (C : Set (Ω × X)) (hC : @MeasurableSet (Ω × X) (m.prod mX) C)
    (E : Set Ω) (hE : MeasurableSet[m] E) (T : Set Ω)
    (r : Ω → ℝ≥0∞)
    (hsections : ∀ ω ∈ E, ν {x | (ω, x) ∈ C} ≤ r ω)
    (hactual : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ T → (ω, Y ω) ∈ C)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    P (A ∩ E ∩ T) ≤ ∫⁻ ω in A ∩ E, r ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  let H : Set Ω := {ω | (ω, Y ω) ∈ C}
  have hH : MeasurableSet H := hC.preimage ((measurable_id'' hm).prodMk hY)
  let K : Ω × X → ℝ≥0∞ := C.indicator (fun _ => 1)
  have hK : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ K := measurable_const.indicator hC
  have hsection (ω : Ω) : (∫⁻ x, K (ω, x) ∂ν) = ν {x | (ω, x) ∈ C} := by
    have hCx : MeasurableSet {x | (ω, x) ∈ C} :=
      hC.preimage (measurable_const.prodMk measurable_id)
    exact lintegral_indicator_one hCx
  calc
    _ ≤ P (A ∩ E ∩ H) := by
      apply measure_mono_ae
      filter_upwards [hactual] with ω hω
      exact fun hmem => ⟨hmem.1, hω hmem.1.2 hmem.2⟩
    _ = ∫⁻ ω in A ∩ E, K (ω, Y ω) ∂P := by
      rw [show (fun ω => K (ω, Y ω)) = H.indicator (fun _ => 1) from rfl,
        setLIntegral_indicator hH, lintegral_one, Measure.restrict_apply_univ]
      rw [inter_comm H]
    _ = ∫⁻ ω in A ∩ E, ∫⁻ x, K (ω, x) ∂ν ∂P :=
      restart_setLIntegral_random_test P ν m hm Y hY hlaw K hK (A ∩ E) (hA.inter hE)
    _ ≤ _ := by
      apply setLIntegral_mono' (hm (A ∩ E) (hA.inter hE))
      intro ω hω
      rw [hsection]
      exact hsections ω hω.2

end SLEExactGauge

end

end OAI
