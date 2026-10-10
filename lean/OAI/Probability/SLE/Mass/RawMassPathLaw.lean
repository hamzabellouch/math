import OAI.Probability.SLE.Mass.CanonicalRawMass
import OAI.Probability.SLE.Mass.RawRadonGoodPaths

namespace OAI

/-! The raw mass has one measurable full-law event carrying all path
properties simultaneously. Equal driver laws therefore preserve these
properties without assuming measurability of an uncountable predicate. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology CompactlySupported NNReal

namespace SLEExactGauge

local instance rawPathLawDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawPathLawDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem exists_raw_rational_radon_factor
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (hNm : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) N)
    (hNr : ∀ t ω, (N t ω).Regular) :
    ∃ μ : ℚ → C(ℝ≥0,ℝ) → Measure upperHalfPlane,
      (∀ q p, (μ q p).Regular) ∧
      (∀ q : ℚ, Measurable[driverPathFiltration (q:ℝ).toNNReal] (μ q)) ∧
      (∀ (q : ℚ) p r, (∀ s ≤ (q:ℝ).toNNReal, p s=r s) → μ q p=μ q r) ∧
      ∀ ω q, μ q (sourceDriverPath B hc ω)=N (q:ℝ).toNNReal ω := by
  choose F hFm hFr hFe using fun q : ℚ => exists_stopped_driver_radon_factor B hm hc
    (q:ℝ).toNNReal (N (q:ℝ).toNNReal) (hNr _) (hNm _)
  refine ⟨fun q p => F q (driverPathStopped (q:ℝ).toNNReal p),?_,?_,?_,?_⟩
  · exact fun q p => hFr q _
  · exact fun q => (hFm q).comp (driverPathStopped_measurable_past (q:ℝ).toNNReal)
  · intro q p r hpr
    exact congrArg (F q) (driverPathStopped_eq_of_agree _ _ le_rfl p r hpr)
  · exact fun ω q => hFe q ω

lemma rational_reconstruction_nonanticipating
    (μ : ℚ → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (hμ : ∀ (q : ℚ) p r, (∀ s ≤ (q:ℝ).toNNReal, p s=r s) → μ q p=μ q r)
    (t : ℝ≥0) (p r : C(ℝ≥0,ℝ)) (hpr : ∀ s ≤ t, p s=r s) :
    rationalRadonExtension μ t p=rationalRadonExtension μ t r := by
  unfold rationalRadonExtension
  apply congrArg canonicalRadonLimit
  funext n
  apply hμ
  intro s hs
  apply hpr s
  apply hs.trans
  simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal (leftRationalSample_le n t)

theorem raw_radon_path_properties_of_same_law
    {Ω Ξ Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Y]
    (P : Measure Ω) (Q : Measure Ξ) (A : Ω → Y) (B : Ξ → Y)
    (hA : Measurable A) (hB : Measurable B) (hlaw : Q.map B=P.map A)
    (D : LocalTestFamily upperHalfPlane) (μ : ℚ → Y → Measure upperHalfPlane)
    (hm : ∀ q, Measurable (μ q)) (hr : ∀ q y, (μ q y).Regular)
    (hg : ∀ᵐ ω ∂P, RawRadonGood D (fun q => μ q (A ω))) :
    ∀ᵐ ξ ∂Q,
      rationalRadonExtension μ 0 (B ξ)=0 ∧
      Monotone (fun t => rationalRadonExtension μ t (B ξ)) ∧
      ∀ f : C_c(upperHalfPlane,ℝ),
        Continuous (fun t => ∫ z, f z ∂rationalRadonExtension μ t (B ξ)) := by
  have hE := measurableSet_rawRadonGood D μ hm hr
  have hpush : ∀ᵐ y ∂P.map A, RawRadonGood D (fun q => μ q y) :=
    (ae_map_iff hA.aemeasurable hE).mpr hg
  rw [← hlaw] at hpush
  have hgood := (ae_map_iff hB.aemeasurable hE).mp hpush
  filter_upwards [hgood] with ξ hξ
  exact RawRadonGood.reconstructed_paths D (fun q => μ q (B ξ)) (fun q => hr q _) hξ

namespace Multipoint

theorem CanonicalMass.exists_raw_nonanticipating_with_good_set
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    ∃ R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane,
      ∃ E : Set C(ℝ≥0,ℝ),
      IsProgressive driverPathFiltration R ∧
      (∀ t p, (R t p).Regular ∧ IsFiniteMeasureOnCompacts (R t p)) ∧
      (∀ t p r, (∀ s ≤ t, p s=r s) → R t p=R t r) ∧
      MeasurableSet E ∧ (∀ᵐ p ∂P.map (sourceDriverPath B hBc), p ∈ E) ∧
      (∀ p ∈ E, R 0 p=0 ∧ Monotone (fun t => R t p) ∧
        ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂(R t p))) ∧
      ∀ᵐ ω ∂P, ∀ t, R t (sourceDriverPath B hBc ω)=C.process t ω := by
  have hm (t : ℝ≥0) : Measurable (B t) :=
    hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨μ,hμr,hμm,hμn,hμe⟩ := exists_raw_rational_radon_factor B hm hBc C.process
    C.progressive.adapted (fun t ω => (C.radon t ω).1)
  let R := rationalRadonExtension μ
  let D := localTestFamily upperHalfPlane
  let E : Set C(ℝ≥0,ℝ) := {p | RawRadonGood D (fun q => μ q p)}
  have hμma (q : ℚ) : Measurable (μ q) :=
    (hμm q).mono (driverPathFiltration.le _) le_rfl
  have hEm : MeasurableSet E := measurableSet_rawRadonGood D μ hμma hμr
  have hgood : ∀ᵐ ω ∂P, sourceDriverPath B hBc ω ∈ E := by
    filter_upwards [C.paths] with ω hω
    dsimp only [E,mem_ofPred_eq]
    simp_rw [hμe]
    exact rawRadonGood_of_continuous_path D (fun t => C.process t ω)
      (fun t => (C.radon t ω).1) hω.zero hω.monotone hω.continuous_tests
  have hbp : Measurable (sourceDriverPath B hBc) := source_path_measurable _ hm
  refine ⟨R,E,rationalRadonExtension_progressive driverPathFiltration μ hμr (fun q _ => hμm q),
    rationalRadonExtension_regular μ,rational_reconstruction_nonanticipating μ hμn,
    hEm,(ae_map_iff hbp.aemeasurable hEm).mpr hgood,?_,?_⟩
  · intro p hp
    exact RawRadonGood.reconstructed_paths D (fun q => μ q p) (fun q => hμr q p) hp
  · let μ' (q : ℚ) (ω : Ω) := μ q (sourceDriverPath B hBc ω)
    have hc : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
        Continuous (fun t : ℝ => ∫ z, f z ∂C.process t.toNNReal ω) := by
      filter_upwards [C.paths] with ω hω
      intro f
      exact (hω.continuous_tests f).comp continuous_real_toNNReal
    have he : ∀ᵐ ω ∂P, ∀ q : ℚ, C.process (q:ℝ).toNNReal ω=μ' q ω :=
      ae_of_all _ (fun ω q => (hμe ω q).symm)
    have h := rationalRadonExtension_common_version P μ' (fun t ω => C.process t.toNNReal ω)
      (fun t ω => (C.radon t.toNNReal ω).1) hc he
    filter_upwards [h] with ω hω
    intro t
    simpa only [R,rationalRadonExtension,μ',Real.toNNReal_coe] using hω t

end Multipoint
end SLEExactGauge

end

end OAI
