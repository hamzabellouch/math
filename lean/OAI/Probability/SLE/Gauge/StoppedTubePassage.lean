import OAI.Probability.SLE.StoppedMeasures
import OAI.Probability.SLE.Geometry.GeometricTubeSupport
import OAI.Probability.SLE.Gauge.VaryingPassageEvents

namespace OAI

/-! Passage after a stopping time from countably many open tube certificates.
The stopped trace law gives independence for each fixed tube. A countable
cover of pasts then gives pointwise positive conditional passage probability;
no common support probability is assumed. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

/-- A fixed positive-law test, certified on a past event, forces the
conditional passage probability to be positive on that event. -/
theorem conditional_passage_positive_on_certificate
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (A C : Set Ω) (hA : MeasurableSet[m] A) (hC : MeasurableSet[mΩ] C)
    (B : Set X) (hB : MeasurableSet B) (hBpos : 0 < ν B)
    (hcert : A ∩ Y ⁻¹' B ⊆ C) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < P⁻[C.indicator (fun _ => 1) | m] ω := by
  let : MeasurableSpace Ω := mΩ
  let q := P⁻[C.indicator (fun _ => 1) | m]
  let Z := A ∩ {ω | q ω = 0}
  have hZ : MeasurableSet[m] Z :=
    hA.inter (measurableSet_eq_fun (measurable_condLExp m P _) measurable_const)
  have hzero : P (Z ∩ C) = 0 := by
    calc
      P (Z ∩ C) = ∫⁻ ω in Z, C.indicator (fun _ => 1) ω ∂P := by
        rw [setLIntegral_indicator hC, setLIntegral_const, one_mul]
        congr 1
        exact inter_comm Z C
      _ = ∫⁻ ω in Z, q ω ∂P := (setLIntegral_condLExp hm P _ hZ).symm
      _ = 0 := by
        apply (setLIntegral_eq_zero_iff (hm Z hZ)
          ((measurable_condLExp m P _).mono hm le_rfl)).mpr
        exact Eventually.of_forall (fun ω hω => hω.2)
  have hproduct : P Z * ν B = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      P Z * ν B = ((P.restrict Z).map Y) B := by
        rw [hlaw Z hZ, Measure.smul_apply, smul_eq_mul]
      _ = P (Y ⁻¹' B ∩ Z) := by
        rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB)]
      _ ≤ P (Z ∩ C) := measure_mono (by
        rintro ω ⟨hωB, hωZ⟩
        exact ⟨hωZ, hcert ⟨hωZ.1, hωB⟩⟩)
      _ = 0 := hzero
  have hZzero : P Z = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right hBpos.ne'
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZzero] with ω hω hωA
  by_contra h
  exact hω ⟨hωA, le_antisymm (not_lt.mp h) bot_le⟩

/-- Countably many past-measurable tube certificates suffice even when
their positive support probabilities depend on the certificate. -/
theorem conditional_passage_positive_of_countable_certificates
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (E C : Set Ω) (hC : MeasurableSet[mΩ] C)
    (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet[m] (A i))
    (B : ℕ → Set X) (hB : ∀ i, MeasurableSet (B i))
    (hBpos : ∀ i, 0 < ν (B i))
    (hcert : ∀ i, A i ∩ Y ⁻¹' B i ⊆ C)
    (hcover : E ⊆ ⋃ i, A i) :
    ∀ᵐ ω ∂P, ω ∈ E → 0 < P⁻[C.indicator (fun _ => 1) | m] ω := by
  let : MeasurableSpace Ω := mΩ
  have hall : ∀ᵐ ω ∂P, ∀ i, ω ∈ A i →
      0 < P⁻[C.indicator (fun _ => 1) | m] ω :=
    ae_all_iff.mpr (fun i => conditional_passage_positive_on_certificate
      P ν m hm Y hY hlaw (A i) C (hA i) hC (B i) (hB i) (hBpos i) (hcert i))
  filter_upwards [hall] with ω hω hωE
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hωE)
  exact hω i hi

/-- The actual Brownian stopped trace law and the published geometric
support input give conditional positivity for countably certified geometric
continuations. The same realization also has the actual conformal restart
identity, so the certificates can be checked in the original domain. -/
theorem stopped_geometric_tube_passages
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hpublished : PublishedGeometricTubeSupport P γ) :
    ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
      (∀ ω, Φ (sourceDriverPath B hc ω) =
        sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      ∀ (τ : Ω → ℝ≥0)
        (hτ : IsStoppingTime
          (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
          (fun ω => (τ ω : WithTop ℝ≥0))),
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Φ (sourceRestartDriverPath B hc τ ω) t ∈ upperHalfPlane →
          γ ω (τ ω + t) = F ω (τ ω)
            (Φ (sourceRestartDriverPath B hc τ ω) t +
              (Real.sqrt κ * B (τ ω) ω : ℝ))) ∧
        ∀ (E C : Set Ω), MeasurableSet[mΩ] C →
        ∀ (A : ℕ → Set Ω), (∀ i, MeasurableSet[hτ.measurableSpace] (A i)) →
        ∀ (z : ℕ → ℂ) (p : ∀ i, Path (0 : ℂ) (z i)),
          (∀ i, Function.Injective (p i)) →
          (∀ i t, t ≠ 0 → p i t ∈ upperHalfPlane) →
        ∀ (N V : ℕ → Set ℂ), (∀ i, IsOpen (N i)) → (∀ i, IsOpen (V i)) →
          (∀ i, range (p i) ⊆ N i) → (∀ i, z i ∈ V i) →
          (∀ i, A i ∩ (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) ⁻¹'
            pathTubeEvent (N i) (V i) ⊆ C) →
          E ⊆ ⋃ i, A i →
          ∀ᵐ ω ∂P, ω ∈ E →
            0 < P⁻[C.indicator (fun _ => 1) | hτ.measurableSpace] ω := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Φ, hΦm, hΦ, hlaw⟩ :=
    sourceStoppedTraceLaw κ hκ hκ8 B hB hm hc γ G F hw
  refine ⟨Φ, hΦm, hΦ, ?_⟩
  intro τ hτ
  refine ⟨(hlaw τ hτ).2, ?_⟩
  intro E C hC A hA z p hp hpH N V hN hV hpN hzV hcert hcover
  let : MeasurableSpace Ω := mΩ
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hgm : Measurable gp := by
    have he : gp = fun ω => Φ (sourceDriverPath B hc ω) := funext fun ω => (hΦ ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable (sourceDriverPath B hc) hm)
  have hrm : Measurable (sourceRestartDriverPath B hc τ) :=
    source_path_measurable _ (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  have htests : ∀ i, 0 < P.map gp (pathTubeEvent (N i) (V i)) := by
    intro i
    rw [Measure.map_apply hgm (measurableSet_pathTubeEvent (hN i) (hV i))]
    exact hpublished (z i) (p i) (hp i) (hpH i) (N i) (V i)
      (hN i) (hV i) (hpN i) (hzV i)
  exact conditional_passage_positive_of_countable_certificates P (P.map gp)
    hτ.measurableSpace hτ.measurableSpace_le
    (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) (hΦm.comp hrm)
    ((hlaw τ hτ).1) E C hC A hA
    (fun i => pathTubeEvent (N i) (V i))
    (fun i => measurableSet_pathTubeEvent (hN i) (hV i)) htests hcert hcover

end SLEExactGauge

end

end OAI
