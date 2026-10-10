import OAI.Probability.SLE.Gauge.CanonicalGridLower

namespace OAI

/-! The finite centered laws give the unit bound for every early cell test. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

def compactFinitePastTest (K : Set upperHalfPlane) (H : ℝ) (J : Finset ℝ≥0) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in (Subtype.val : upperHalfPlane → ℂ) '' K,
    ENNReal.ofReal (initialGreen κ x) * finiteCenteredLaw P κ B γ G x u
      (finiteStrictPastEvent J (fun t => {ω | H < (C.process t ω K).toReal})
        (fun ω => radiusLevelTime (γ ω) (G ω) x u)) ∂volume

lemma compactFinitePastTest_le_initial
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (K : Set upperHalfPlane) (hK : IsCompact K) (H : ℝ) (J : Finset ℝ≥0)
    (u : ℝ) (hu : 0≤u) : C.compactFinitePastTest K H J u ≤ initialGreenMeasure κ K := by
  have hKI := (hK.image continuous_subtype_val).measurableSet
  rw [initialGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hKI]
  apply setLIntegral_mono' hKI
  rintro x ⟨z,_,rfl⟩
  let := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F (Eventually.of_forall hw)
    (z:ℂ) z.property u hu
  have hQ : finiteCenteredLaw P κ B γ G (z:ℂ) u
      (finiteStrictPastEvent J (fun t => {ω | H < (C.process t ω K).toReal})
        (fun ω => radiusLevelTime (γ ω) (G ω) (z:ℂ) u)) ≤ 1 := by
    calc
      _ ≤ finiteCenteredLaw P κ B γ G (z:ℂ) u univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (initialGreen κ z))) hQ

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
