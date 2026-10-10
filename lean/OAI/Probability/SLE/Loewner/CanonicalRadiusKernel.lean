import OAI.Probability.SLE.Geometry.JointRadiusKernel
import OAI.Probability.SLE.Geometry.CanonicalRestartWitness

namespace OAI

/-! The radius kernels on continuous driver space. The measurable functions
are fixed independently of any probability law or marked point. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance radiusDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance radiusDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def canonicalRadiusFamily (κ : ℝ) :
    SpatialClippedFamily (fun (t : ℝ≥0) (p : C(ℝ≥0, ℝ)) => Real.sqrt κ * p t) :=
  spatialClippedFamily _
    (((continuous_eval.comp (continuous_snd.prodMk continuous_fst)).measurable).const_mul _)
    (fun p => p.continuous.const_mul _)

def canonicalRadius (κ : ℝ) : ℝ≥0 × (ℂ × C(ℝ≥0, ℝ)) → ℝ :=
  (canonicalRadiusFamily κ).jointRadius

def canonicalRadiusLevel (κ : ℝ) : ℝ × (ℂ × C(ℝ≥0, ℝ)) → ℝ≥0∞ :=
  (canonicalRadiusFamily κ).jointRadiusLevel

lemma canonicalRadius_measurable (κ : ℝ) : Measurable (canonicalRadius κ) :=
  (canonicalRadiusFamily κ).jointRadius_measurable

lemma canonicalRadiusLevel_measurable (κ : ℝ) : Measurable (canonicalRadiusLevel κ) :=
  (canonicalRadiusFamily κ).jointRadiusLevel_measurable

lemma canonicalRadius_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (t : ℝ≥0) (z : ℂ) :
    canonicalRadius κ (t, z, p) =
      if z ∈ survivingDomain γ t then fullRadius G t z else 0 :=
  (canonicalRadiusFamily κ).jointRadius_eq p (p.continuous.const_mul _) hw t z

lemma canonicalRadiusLevel_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    canonicalRadiusLevel κ (u, z, p) = radiusLevelTime γ G z u :=
  (canonicalRadiusFamily κ).jointRadiusLevel_eq p (p.continuous.const_mul _) hw u hu z

lemma measurable_canonicalRadiusLevel_random_state
    {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ)
    {Y : Ω → C(ℝ≥0, ℝ)} (hY : Measurable Y)
    {u : Ω → ℝ} (hu : Measurable u) {z : Ω → ℂ} (hz : Measurable z) :
    Measurable (fun ω => canonicalRadiusLevel κ (u ω, z ω, Y ω)) :=
  (canonicalRadiusLevel_measurable κ).comp (hu.prodMk (hz.prodMk hY))

/-- A random measurable marked state has an actual radius-level time with a
measurable version, with no point-dependent selection of an exceptional set. -/
theorem aemeasurable_radiusLevelTime_random_state
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (κ : ℝ)
    {Y : Ω → C(ℝ≥0, ℝ)} (hY : Measurable Y)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * Y ω t) (γ ω) (G ω) (F ω))
    {u : Ω → ℝ} (hum : Measurable u) (hu : ∀ᵐ ω ∂P, 0 ≤ u ω)
    {z : Ω → ℂ} (hz : Measurable z) :
    AEMeasurable (fun ω => radiusLevelTime (γ ω) (G ω) (z ω) (u ω)) P := by
  apply (measurable_canonicalRadiusLevel_random_state κ hY hum hz).aemeasurable.congr
  filter_upwards [hw, hu] with ω hω huω
  exact canonicalRadiusLevel_eq κ (Y ω) hω (u ω) huω (z ω)

/-- The same fixed kernel applies to any random driver with the canonical
driver law, including the actual post-stopping driver. -/
theorem canonicalRadiusLevel_same_law_witness
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ν : Measure C(ℝ≥0, ℝ)) (κ : ℝ)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    (Y : Ω → C(ℝ≥0, ℝ)) (hY : Measurable Y) (hlaw : P.map Y = ν) :
    ∀ᵐ ω ∂P, ∀ u, 0 ≤ u → ∀ z,
      canonicalRadiusLevel κ (u, z, Y ω) =
        radiusLevelTime (Φ (Y ω)) (Gc (Y ω)) z u := by
  have hW := canonical_witness_pullback hw Y hY hlaw
  filter_upwards [hW] with ω hω
  exact fun u hu z => canonicalRadiusLevel_eq κ (Y ω) hω u hu z

def canonicalGreen (κ : ℝ) : ℝ≥0 × (ℂ × C(ℝ≥0, ℝ)) → ℝ :=
  (canonicalRadiusFamily κ).jointGreen κ (fun t p => p t)

lemma canonicalGreen_measurable (κ : ℝ) : Measurable (canonicalGreen κ) :=
  (canonicalRadiusFamily κ).jointGreen_measurable κ (fun t p => p t)
    (continuous_eval.comp (continuous_snd.prodMk continuous_fst)).measurable

lemma canonicalGreen_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (t : ℝ≥0) (z : ℂ) :
    canonicalGreen κ (t, z, p) =
      greenDensity κ (fun t => Real.sqrt κ * p t) γ G t z :=
  (canonicalRadiusFamily κ).jointGreen_eq κ (fun t p => p t) p
    (p.continuous.const_mul _) (fun _ => rfl) hw t z

def canonicalStoppedGreen (κ : ℝ) (p : ℝ × (ℂ × C(ℝ≥0, ℝ))) : ℝ :=
  if canonicalRadiusLevel κ p < ∞ then
    canonicalGreen κ ((canonicalRadiusLevel κ p).toNNReal, p.2)
  else 0

lemma canonicalStoppedGreen_measurable (κ : ℝ) : Measurable (canonicalStoppedGreen κ) := by
  apply Measurable.ite (measurableSet_lt (canonicalRadiusLevel_measurable κ) measurable_const)
    _ measurable_const
  exact (canonicalGreen_measurable κ).comp
    ((ENNReal.measurable_toNNReal.comp (canonicalRadiusLevel_measurable κ)).prodMk measurable_snd)

lemma canonicalStoppedGreen_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    canonicalStoppedGreen κ (u, z, p) =
      stoppedGreen κ (fun t => Real.sqrt κ * p t) γ G z u := by
  unfold canonicalStoppedGreen
  rw [canonicalRadiusLevel_eq κ p hw u hu z]
  unfold stoppedGreen
  split_ifs
  · exact canonicalGreen_eq κ p hw _ z
  · rfl

def canonicalFiniteDensity (κ : ℝ) (p : ℝ × (ℂ × C(ℝ≥0, ℝ))) : ℝ≥0∞ :=
  ENNReal.ofReal (canonicalStoppedGreen κ p / initialGreen κ p.2.1)

lemma canonicalFiniteDensity_measurable (κ : ℝ) : Measurable (canonicalFiniteDensity κ) := by
  have hinit : Measurable (initialGreen κ) := by
    unfold initialGreen
    fun_prop
  exact ENNReal.measurable_ofReal.comp
    ((canonicalStoppedGreen_measurable κ).div
      (hinit.comp (measurable_fst.comp measurable_snd)))

lemma canonicalFiniteDensity_eq (κ : ℝ) (p : C(ℝ≥0, ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    canonicalFiniteDensity κ (u, z, p) = ENNReal.ofReal
      (stoppedGreen κ (fun t => Real.sqrt κ * p t) γ G z u / initialGreen κ z) := by
  simp only [canonicalFiniteDensity, canonicalStoppedGreen_eq κ p hw u hu z]

/-- The tilted-density kernel is jointly measurable in level, marked point,
and driver, and represents the actual density on one common full-measure set. -/
theorem canonical_density_same_law_witness
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ν : Measure C(ℝ≥0, ℝ)) (κ : ℝ)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    (Y : Ω → C(ℝ≥0, ℝ)) (hY : Measurable Y) (hlaw : P.map Y = ν) :
    ∀ᵐ ω ∂P, ∀ u, 0 ≤ u → ∀ z,
      canonicalStoppedGreen κ (u, z, Y ω) =
        stoppedGreen κ (fun t => Real.sqrt κ * Y ω t) (Φ (Y ω)) (Gc (Y ω)) z u ∧
      canonicalFiniteDensity κ (u, z, Y ω) = ENNReal.ofReal
        (stoppedGreen κ (fun t => Real.sqrt κ * Y ω t)
          (Φ (Y ω)) (Gc (Y ω)) z u / initialGreen κ z) := by
  have hW := canonical_witness_pullback hw Y hY hlaw
  filter_upwards [hW] with ω hω
  exact fun u hu z => ⟨canonicalStoppedGreen_eq κ (Y ω) hω u hu z,
    canonicalFiniteDensity_eq κ (Y ω) hω u hu z⟩

lemma measurable_canonicalFiniteDensity_random_state
    {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ)
    {Y : Ω → C(ℝ≥0, ℝ)} (hY : Measurable Y)
    {u : Ω → ℝ} (hu : Measurable u) {z : Ω → ℂ} (hz : Measurable z) :
    Measurable (fun ω => canonicalFiniteDensity κ (u ω, z ω, Y ω)) :=
  (canonicalFiniteDensity_measurable κ).comp (hu.prodMk (hz.prodMk hY))

theorem canonical_finiteCenteredLaw_eq
    (ν : Measure C(ℝ≥0, ℝ)) (κ : ℝ)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    finiteCenteredLaw ν κ (fun t p => p t) (fun p t => Φ p t) Gc z u =
      ν.withDensity (fun p => canonicalFiniteDensity κ (u, z, p)) := by
  unfold finiteCenteredLaw
  apply withDensity_congr_ae
  filter_upwards [hw] with p hp
  exact (canonicalFiniteDensity_eq κ p hp u hu z).symm

end SLEExactGauge

end

end OAI
