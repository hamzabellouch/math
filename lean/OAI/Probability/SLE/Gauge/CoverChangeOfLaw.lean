import OAI.Probability.SLE.FiniteStoppedLaw
import OAI.Probability.SLE.Gauge.DenseCoverCore

namespace OAI

/-!
The finite-stop change of measure in the missed-cell estimate of
`prop:dense-cover-upper`, *An explicit exact Hausdorff gauge for SLE*.

A conditional approach estimate is the hypothesis for the conditioning
and change-of-law steps.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SLEExactGauge

/-- Restricting a normalized density to an event exactly recovers its
unnormalized integral. No measurability of the density is needed here. -/
theorem setLIntegral_eq_mul_normalizedDensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : Ω → ℝ) {a : ℝ} (ha : 0 < a) {A : Set Ω} (hA : MeasurableSet A) :
    (∫⁻ ω in A, ENNReal.ofReal (w ω) ∂P) =
      ENNReal.ofReal a *
        P.withDensity (fun ω => ENNReal.ofReal (w ω / a)) A := by
  rw [withDensity_apply _ hA,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro ω
  rw [ENNReal.ofReal_div_of_pos ha,
    ENNReal.mul_div_cancel (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top]

/-- The precise event identity for the finite centered law, at a fixed
logarithmic conformal-radius stop. -/
theorem finiteCenteredLaw_event_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (G : Ω → ℝ≥0 → ℂ → ℂ) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (u : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    (∫⁻ ω in A, ENNReal.ofReal
      (stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u) ∂P) =
      ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z u A :=
  setLIntegral_eq_mul_normalizedDensity P _ (initialGreen_pos κ z hz) hA

/-- A conditional approach bound can be integrated on any event determined
by the conditioning sigma algebra. The smaller event need not be measurable. -/
theorem measure_le_setLIntegral_of_conditional_approach
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {E V A : Set Ω} (hV : MeasurableSet[mΩ] V) (hA : MeasurableSet[m] A)
    (hE : E ⊆ V ∩ A) (W : Ω → ℝ≥0∞) (K : ℝ≥0∞) (hK : K ≠ ∞)
    (happroach : ∀ᵐ ω ∂P, ω ∈ A →
      P⁻[V.indicator (fun _ => 1) | m] ω ≤ K * W ω) :
    P E ≤ K * ∫⁻ ω in A, W ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  calc
    P E ≤ P (V ∩ A) := measure_mono hE
    _ = ∫⁻ ω in A, V.indicator (fun _ => 1) ω ∂P := by
      rw [setLIntegral_indicator hV, setLIntegral_const, one_mul]
    _ = ∫⁻ ω in A, P⁻[V.indicator (fun _ => 1) | m] ω ∂P :=
      (setLIntegral_condLExp hm P _ hA).symm
    _ ≤ ∫⁻ ω in A, K * W ω ∂P :=
      lintegral_mono_ae ((ae_restrict_iff' (hm A hA)).mpr happroach)
    _ = K * ∫⁻ ω in A, W ω ∂P := lintegral_const_mul' K W hK

/-- Transfer a visited cell with no candidate from the original law to a
finite centered law. `A` is the adapted failure event and `V` the visit event.
The displayed conditional approach bound is the only probabilistic estimate
assumed by this reduction. -/
theorem finiteCenteredLaw_missed_cell_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (G : Ω → ℝ≥0 → ℂ → ℂ) (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {E V A : Set Ω} (hV : MeasurableSet[mΩ] V) (hA : MeasurableSet[m] A)
    (hE : E ⊆ V ∩ A) (C r p : ℝ)
    (happroach : ∀ᵐ ω ∂P, ω ∈ A →
      P⁻[V.indicator (fun _ => 1) | m] ω ≤ ENNReal.ofReal (C * r ^ p) *
        ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
          (γ ω) (G ω) z u)) :
    P E ≤ ENNReal.ofReal (C * r ^ p) * ENNReal.ofReal (initialGreen κ z) *
      @finiteCenteredLaw Ω mΩ P κ B γ G z u A := by
  let : MeasurableSpace Ω := mΩ
  have h := measure_le_setLIntegral_of_conditional_approach P m hm hV hA hE
    (fun ω => ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u)) (ENNReal.ofReal (C * r ^ p)) ENNReal.ofReal_ne_top happroach
  rw [finiteCenteredLaw_event_identity P κ B γ G z hz u (hm A hA)] at h
  simpa only [mul_assoc] using h

/-- Any tilted-law failure estimate, in particular the stretched exponential
bound from repeated adapted tests, gives the corresponding missed-cell bound. -/
theorem finiteCenteredLaw_missed_cell_bound_of_failure_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (G : Ω → ℝ≥0 → ℂ → ℂ) (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {E V A : Set Ω} (hV : MeasurableSet[mΩ] V) (hA : MeasurableSet[m] A)
    (hE : E ⊆ V ∩ A) (C r p : ℝ) (ε : ℝ≥0∞)
    (happroach : ∀ᵐ ω ∂P, ω ∈ A →
      P⁻[V.indicator (fun _ => 1) | m] ω ≤ ENNReal.ofReal (C * r ^ p) *
        ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
          (γ ω) (G ω) z u))
    (hfailure : @finiteCenteredLaw Ω mΩ P κ B γ G z u A ≤ ε) :
    P E ≤ ENNReal.ofReal (C * r ^ p) * ENNReal.ofReal (initialGreen κ z) * ε := by
  let : MeasurableSpace Ω := mΩ
  exact (finiteCenteredLaw_missed_cell_bound P κ B γ G z hz u m hm hV hA hE
    C r p happroach).trans (mul_le_mul' le_rfl hfailure)

/-- The failure probability is a product bound under the centered law; no
independence assumption is used. -/
theorem finiteCenteredLaw_adapted_failures_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (filtration : Filtration ℕ mΩ) (failure : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet[filtration (n + 1)] (failure n))
    (q : ℝ≥0∞)
    (hstep : ∀ n (A : Set Ω), MeasurableSet[filtration n] A →
      finiteCenteredLaw P κ B γ G z u (A ∩ failure n) ≤
        q * finiteCenteredLaw P κ B γ G z u A)
    (N : ℕ) {A : Set Ω} (hA : A ⊆ ⋂ n ∈ Finset.range N, failure n) :
    finiteCenteredLaw P κ B γ G z u A ≤ q ^ N := by
  let := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F hw z hz u hu
  calc
    finiteCenteredLaw P κ B γ G z u A ≤
        finiteCenteredLaw P κ B γ G z u (⋂ n ∈ Finset.range N, failure n) :=
      measure_mono hA
    _ ≤ q ^ N * finiteCenteredLaw P κ B γ G z u univ :=
      adapted_failures_bound _ filtration failure hmeas q hstep N
    _ = q ^ N := by rw [measure_univ, mul_one]

end SLEExactGauge

end

end OAI
