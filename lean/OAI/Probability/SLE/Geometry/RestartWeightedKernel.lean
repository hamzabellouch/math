import OAI.Probability.SLE.Geometry.RandomRestartEvents

namespace OAI

/-! Integration of measurable marked-state density kernels against the
actual independent restarted driver. This is used with the proved centered
SLE section bounds and the deterministic restarted Green-density bound. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

theorem restart_setLIntegral_random_test
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (f : Ω × X → ℝ≥0∞) (hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ f)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    (∫⁻ ω in A, f (ω, Y ω) ∂P) = ∫⁻ ω in A, ∫⁻ x, f (ω, x) ∂ν ∂P := by
  let : MeasurableSpace Ω := mΩ
  let fA : Ω × X → ℝ≥0∞ := (A ×ˢ (univ : Set X)).indicator f
  have hfA : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ fA :=
    hf.indicator (hA.prod MeasurableSet.univ)
  have he := @restart_lintegral_random_test Ω X mΩ mX P inferInstance ν inferInstance
    m hm Y hY hlaw fA hfA
  have hleft : (fun ω => fA (ω, Y ω)) = A.indicator (fun ω => f (ω, Y ω)) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [fA, hω]
  have hright : (fun ω => ∫⁻ x, fA (ω, x) ∂ν) =
      A.indicator (fun ω => ∫⁻ x, f (ω, x) ∂ν) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [fA, hω]
  rw [hleft, hright, lintegral_indicator (hm A hA), lintegral_indicator (hm A hA)] at he
  exact he

/-- A lower section bound gives a lower tilted probability on every event
in the stopped past. The density domination is pointwise along the actual
fresh driver and is supplied by Loewner restart composition. -/
theorem restart_weighted_event_lower_bound
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (K : Ω × X → ℝ≥0∞) (hK : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ K)
    (C : Set (Ω × X)) (hC : @MeasurableSet (Ω × X) (m.prod mX) C)
    (V Z : Ω → ℝ≥0∞) (q : ℝ≥0∞) (hq : q ≠ ∞)
    (E : Set Ω) (hE : MeasurableSet[mΩ] E)
    (hsections : ∀ᵐ ω ∂P, q * V ω ≤ ∫⁻ x, C.indicator K (ω, x) ∂ν)
    (hactual : ∀ᵐ ω ∂P, C.indicator K (ω, Y ω) ≤ E.indicator Z ω)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    q * (∫⁻ ω in A, V ω ∂P) ≤ P.withDensity Z (A ∩ E) := by
  let : MeasurableSpace Ω := mΩ
  calc
    _ = ∫⁻ ω in A, q * V ω ∂P := (lintegral_const_mul' q V hq).symm
    _ ≤ ∫⁻ ω in A, ∫⁻ x, C.indicator K (ω, x) ∂ν ∂P :=
      lintegral_mono_ae (ae_restrict_of_ae hsections)
    _ = ∫⁻ ω in A, C.indicator K (ω, Y ω) ∂P :=
      (restart_setLIntegral_random_test P ν m hm Y hY hlaw (C.indicator K)
        (hK.indicator hC) A hA).symm
    _ ≤ ∫⁻ ω in A, E.indicator Z ω ∂P := lintegral_mono_ae (ae_restrict_of_ae hactual)
    _ = P.withDensity Z (A ∩ E) := by
      rw [setLIntegral_indicator hE, inter_comm, withDensity_apply _ ((hm A hA).inter hE)]

end SLEExactGauge

end

end OAI
