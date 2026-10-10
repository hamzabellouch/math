import OAI.Probability.SLE.Geometry.FiniteBoundaryRestart
import OAI.Probability.SLE.Geometry.BoundaryScaleLaw
import OAI.Probability.SLE.Gauge.CoverChangeOfLaw
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

namespace OAI

/-! Quantitative passage bounds for measurable random stopped charts and
finite stopped changes of measure. These are integration identities, with
the actual section estimates supplied by the ribbon proof. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open BoundaryScaleLaw

local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace
local instance randomPassagePathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance randomPassagePathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance randomPassageClosedMeasurable : MeasurableSpace C(ℝ≥0, closedHalfPlane) := borel _
local instance randomPassageClosedBorel : BorelSpace C(ℝ≥0, closedHalfPlane) := ⟨rfl⟩

lemma measurable_random_finiteBoundaryPath
    {Ω : Type*} [MeasurableSpace Ω]
    (Fb : Ω → C(closedHalfPlane, ℂ)) (hFb : Measurable Fb) :
    Measurable (fun x : Ω × C(ℝ≥0, ℂ) => finiteBoundaryPath (Fb x.1) x.2) := by
  have hc : Continuous (fun x : C(ℝ≥0, closedHalfPlane) × C(closedHalfPlane, ℂ) =>
      x.2.comp x.1) := ContinuousMap.continuous_comp'
  exact hc.measurable.comp
    ((measurable_liftClosedPath.comp measurable_snd).prodMk (hFb.comp measurable_fst))

lemma measurableSet_random_finite_frontMassEvent
    {Ω : Type*} [MeasurableSpace Ω]
    (Fb : Ω → C(closedHalfPlane, ℂ)) (hFb : Measurable Fb)
    (p : ℂ → ℝ) (V : Set ℂ) (a : ℂ) (ε κ v c : ℝ) (R K : Set ℂ)
    (hK : IsClosed K) (hp : ContinuousOn p K) (hV : IsOpen V) (hVK : V ⊆ K) :
    MeasurableSet {x : Ω × C(ℝ≥0, ℂ) |
      finiteBoundaryPath (Fb x.1) x.2 ∈ frontMassEvent p V a ε κ v c R} :=
  (measurableSet_frontMassEvent p V a ε κ v c R K hK hp hV hVK).preimage
    (measurable_random_finiteBoundaryPath Fb hFb)

lemma restart_condLExp_event_sections
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (C : Set (Ω × X)) (hC : @MeasurableSet (Ω × X) (m.prod mX) C) :
    (fun ω => ν {x | (ω, x) ∈ C}) =ᵐ[P]
      P⁻[({ω | (ω, Y ω) ∈ C}).indicator (fun _ => 1) | m] := by
  have hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ (C.indicator (fun _ => 1)) := by
    let : MeasurableSpace (Ω × X) := m.prod mX
    exact measurable_const.indicator hC
  let : MeasurableSpace Ω := mΩ
  have he := @restart_condLExp_random_test Ω X mΩ mX P inferInstance ν inferInstance m hm Y hY hlaw
    (C.indicator (fun _ => 1)) hf
  have hs (ω : Ω) : (∫⁻ x, C.indicator (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂ν) =
      ν {x | (ω, x) ∈ C} := by
    change (∫⁻ x, ({x | (ω, x) ∈ C}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν) = _
    have hsec : MeasurableSet {x | (ω, x) ∈ C} :=
      hC.preimage measurable_prodMk_left
    rw [lintegral_indicator hsec, setLIntegral_const, one_mul]
  have hind : (fun ω => C.indicator (fun _ => (1 : ℝ≥0∞)) (ω, Y ω)) =
      ({ω | (ω, Y ω) ∈ C}).indicator (fun _ => 1) := by
    funext ω
    by_cases h : (ω, Y ω) ∈ C <;> simp [h]
  simpa only [hs, hind] using he

/-- Uniform section bounds integrate on every event in the stopped past.
No countable list of possible pasts and no independence of steps is used. -/
theorem restart_event_lower_bound
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (C : Set (Ω × X)) (hC : @MeasurableSet (Ω × X) (m.prod mX) C)
    (E : Set Ω) (q : ℝ≥0∞)
    (hsections : ∀ᵐ ω ∂P, ω ∈ E → q ≤ ν {x | (ω, x) ∈ C})
    (A : Set Ω) (hA : MeasurableSet[m] A) (hAE : A ⊆ E) :
    q * P A ≤ P (A ∩ {ω | (ω, Y ω) ∈ C}) := by
  let : MeasurableSpace Ω := mΩ
  have he := @restart_condLExp_event_sections Ω X mΩ mX P inferInstance ν inferInstance m hm Y hY hlaw C hC
  have hactual : MeasurableSet[mΩ] {ω | (ω, Y ω) ∈ C} :=
    hC.preimage ((measurable_id'' hm).prodMk hY)
  calc
    _ = ∫⁻ ω in A, q ∂P := (setLIntegral_const A q).symm
    _ ≤ ∫⁻ ω in A, P⁻[({ω | (ω, Y ω) ∈ C}).indicator (fun _ => 1) | m] ω ∂P := by
      apply lintegral_mono_ae
      apply (ae_restrict_iff' (hm A hA)).mpr
      filter_upwards [he, hsections] with ω hω hsec hωA
      exact hω ▸ hsec (hAE hωA)
    _ = ∫⁻ ω in A, ({ω | (ω, Y ω) ∈ C}).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P :=
      setLIntegral_condLExp hm P _ hA
    _ = P (A ∩ {ω | (ω, Y ω) ∈ C}) := by
      rw [setLIntegral_indicator hactual, setLIntegral_const, one_mul, inter_comm]

/-- A lower bound on the density at a finite stop transfers any event
observable there to the terminal tilted law. -/
theorem normalizedDensity_event_lower_bound_of_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Z M : Ω → ℝ) (hZ : Integrable Z P) (hZpos : 0 ≤ᵐ[P] Z)
    (hM : M =ᵐ[P] P[Z | m])
    (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (E : Set Ω) (hE : MeasurableSet[m] E)
    (hbound : ∀ᵐ ω ∂P, ω ∈ E → c * a ≤ M ω) :
    ENNReal.ofReal c * P E ≤
      P.withDensity (fun ω => ENNReal.ofReal (Z ω / a)) E := by
  let : MeasurableSpace Ω := mΩ
  have hcond := condLExp_ofReal m hZ hZpos
  have hmass : ENNReal.ofReal (c * a) * P E ≤ ∫⁻ ω in E, ENNReal.ofReal (Z ω) ∂P := by
    calc
      _ = ∫⁻ ω in E, ENNReal.ofReal (c * a) ∂P := (setLIntegral_const E _).symm
      _ ≤ ∫⁻ ω in E, P⁻[(fun ω => ENNReal.ofReal (Z ω)) | m] ω ∂P := by
        apply lintegral_mono_ae
        apply (ae_restrict_iff' (hm E hE)).mpr
        filter_upwards [hcond, hM, hbound] with ω hω hMω hb hωE
        rw [hω, ← hMω]
        exact ENNReal.ofReal_le_ofReal (hb hωE)
      _ = _ := setLIntegral_condLExp hm P _ hE
  rw [setLIntegral_eq_mul_normalizedDensity P Z ha (hm E hE),
    ENNReal.ofReal_mul hc, mul_comm (ENNReal.ofReal c), mul_assoc] at hmass
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr ha)
    ENNReal.ofReal_ne_top).mp (by simpa only [mul_comm (ENNReal.ofReal a)] using hmass)

end SLEExactGauge

end

end OAI
