import OAI.Probability.SLE.Mass.CanonicalMassConstruction
import OAI.Probability.SLE.Geometry.RandomSpatialTestingAE

namespace OAI

/-! The positive remaining mass and its conditional random spatial tests.
The stopping-time sigma algebra is the original, uncompleted one. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

namespace CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

def atTime (t : ℝ≥0∞) (ω : Ω) : Measure upperHalfPlane :=
  extendedCanonicalMass C.process C.rational.terminal t ω

lemma atTime_radon (t : ℝ≥0∞) (ω : Ω) :
    (C.atTime t ω).Regular ∧ IsFiniteMeasureOnCompacts (C.atTime t ω) :=
  extendedCanonicalMass_radon C.process C.rational.terminal C.radon C.rational.terminal_radon t ω

lemma atTime_measurable (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun ω => C.atTime (S ω) ω) :=
  extendedCanonicalMass_measurable _ _ _ C.progressive C.rational.terminal_measurable S hS

lemma atTime_le_terminal (S : Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, C.atTime (S ω) ω ≤ C.rational.terminal ω := by
  filter_upwards [C.paths] with ω hω
  dsimp only [atTime,extendedCanonicalMass]
  split_ifs
  · exact hω.dominated _
  · exact le_rfl

lemma atTime_mean_le (S : Ω → ℝ≥0∞) (hS : Measurable S) (E : Set Ω) :
    (P.restrict E).bind (fun ω => C.atTime (S ω) ω) ≤ initialGreenMeasure κ := by
  have hh := restricted_bind_le_of_ae_le P _ _ (C.atTime_measurable S hS)
    C.rational.terminal_measurable (C.atTime_le_terminal S) E
  rwa [C.rational.mean] at hh

theorem exists_remaining_kernel (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S) :
    ∃ η : Ω → Measure upperHalfPlane, Measurable η ∧
      (∀ ω, (η ω).Regular ∧ IsFiniteMeasureOnCompacts (η ω)) ∧
      (∀ᵐ ω ∂P, η ω + C.atTime (S ω) ω = C.rational.terminal ω) ∧
      ∀ E : Set Ω, MeasurableSet[hS.measurableSpace] E →
        (P.restrict E).bind η = (P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S) := by
  obtain ⟨η,hηm,hηr,hηsum⟩ := exists_measurable_halfPlane_difference P C.rational.terminal
    (fun ω => C.atTime (S ω) ω) C.rational.terminal_measurable (C.atTime_measurable S hS.measurable')
    (fun ω => (C.rational.terminal_radon ω).1) (fun ω => (C.atTime_radon (S ω) ω).1)
    (C.atTime_le_terminal S)
  refine ⟨η,hηm,hηr,hηsum,?_⟩
  intro E hE
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind (fun ω => C.atTime (S ω) ω)) :=
    ⟨fun K hK => lt_of_le_of_lt (C.atTime_mean_le S hS.measurable' E K) hK.measure_lt_top⟩
  exact bind_remainder_eq_of_sum (P.restrict E) _ _ η (C.atTime_measurable S hS.measurable')
    C.rational.terminal_measurable hηm _ (ae_restrict_of_ae hηsum) (C.kernel S hS E hE)

/-- The kernel permits all nonnegative tests jointly measurable in the
original stopped past and the spatial point, with arbitrary compact support. -/
theorem exists_remaining_random_tests
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S) :
    ∃ η : Ω → Measure upperHalfPlane, Measurable η ∧
      (∀ ω, (η ω).Regular ∧ IsFiniteMeasureOnCompacts (η ω)) ∧
      (∀ᵐ ω ∂P, η ω + C.atTime (S ω) ω = C.rational.terminal ω) ∧
      ∀ K : Set upperHalfPlane, IsCompact K → ∀ f : Ω × upperHalfPlane → ℝ≥0∞,
        Measurable[hS.measurableSpace.prod inferInstance] f →
        (∫⁻ ω, (∫⁻ z in K, f (ω,z) ∂η ω) ∂P) =
        ∫⁻ ω, (∫⁻ z in K, f (ω,z) ∂halfPlaneStoppingGreenMeasure κ B γ G S ω) ∂P := by
  obtain ⟨η,hηm,hηr,hηsum,hηkernel⟩ := C.exists_remaining_kernel S hS
  have hηdom : ∀ᵐ ω ∂P, η ω ≤ C.rational.terminal ω := by
    filter_upwards [hηsum] with ω hω
    rw [← hω]
    apply Measure.le_iff.mpr
    intro A _
    simp only [Measure.add_apply]
    exact le_add_right le_rfl
  have hηmean : P.bind η ≤ initialGreenMeasure κ := by
    have hh := restricted_bind_le_of_ae_le P η C.rational.terminal hηm
      C.rational.terminal_measurable hηdom univ
    simpa only [Measure.restrict_univ,C.rational.mean] using hh
  have hGm := halfPlaneStoppingGreenMeasure_measurable hBm hBc κ γ G F hw S hS.measurable'
  have hGeq : P.bind η = P.bind (halfPlaneStoppingGreenMeasure κ B γ G S) := by
    simpa only [Measure.restrict_univ] using hηkernel univ MeasurableSet.univ
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  refine ⟨η,hηm,hηr,hηsum,?_⟩
  intro K hK f hf
  have hηK : P.bind η K < ∞ := lt_of_le_of_lt (hηmean K) hK.measure_lt_top
  have hGK : ∀ᵐ ω ∂P, halfPlaneStoppingGreenMeasure κ B γ G S ω K < ∞ := by
    apply ae_lt_top (μ := P) ((Measure.measurable_coe hK.measurableSet).comp hGm)
    change (∫⁻ ω, halfPlaneStoppingGreenMeasure κ B γ G S ω K ∂P) ≠ ∞
    rw [← Measure.bind_apply hK.measurableSet hGm.aemeasurable,← hGeq]
    exact hηK.ne
  exact conditional_random_spatial_test_on_ae hS.measurableSpace hS.measurableSpace_le P
    η (halfPlaneStoppingGreenMeasure κ B γ G S) hηm hGm K hK.measurableSet
    (ae_of_all _ (fun ω => by let := (hηr ω).2; exact hK.measure_lt_top)) hGK hηK
    hηkernel f hf

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
