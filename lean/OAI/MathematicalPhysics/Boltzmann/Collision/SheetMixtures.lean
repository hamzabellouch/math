import OAI.MathematicalPhysics.Boltzmann.Collision.AxialAtomicSheet

namespace OAI

/-!
# Tightness and axial nonconcentration for sheet mixtures

The full kernel depends linearly on its incoming measure. Consequently the
same tail bound and axial modulus hold for the probability mixtures allowed
by the manuscript's sheet class.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.SheetClass
open BoltzmannNonuniqueness.SheetTightness
open BoltzmannNonuniqueness.AxialModulus

namespace BoltzmannNonuniqueness.SheetMixtures

def regionFiber (h : Velocity → ℝ≥0∞) (v : Velocity) (S : Set Coordinates)
    (p : Velocity) : ℝ≥0∞ :=
  ∫⁻ zs : ℝ × ℝ, S.indicator (density h v) (p, zs) ∂(volume.prod volume)

theorem measurable_regionFiber {h : Velocity → ℝ≥0∞} (hh : Measurable h)
    (v : Velocity) {S : Set Coordinates} (hS : MeasurableSet S) :
    Measurable (regionFiber h v S) :=
  ((measurable_density hh v).indicator hS).lintegral_prod_right'

theorem measure_eq_regionFiber (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) {S : Set Coordinates} (hS : MeasurableSet S) :
    ChartKernel.measure c h v S = ∫⁻ p, regionFiber h v S p ∂c := by
  rw [ChartKernel.measure, withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ ((measurable_density hh v).indicator hS).aemeasurable]
  rfl

theorem measure_bind_apply {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
    {M : ι → Measure Velocity} (hM : Measurable M)
    {h : Velocity → ℝ≥0∞} (hh : Measurable h) (v : Velocity)
    {S : Set Coordinates} (hS : MeasurableSet S) :
    ChartKernel.measure (ν.bind M) h v S = ∫⁻ i, ChartKernel.measure (M i) h v S ∂ν := by
  rw [measure_eq_regionFiber _ hh v hS,
    Measure.lintegral_bind hM.aemeasurable (measurable_regionFiber hh v hS).aemeasurable]
  simp_rw [← measure_eq_regionFiber _ hh v hS]

theorem normalized_bind_apply {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
    {M : ι → Measure Velocity} (hM : Measurable M) (q : ℝ) (v : Velocity)
    {S : Set Coordinates} (hS : MeasurableSet S) :
    normalizedMeasure (ν.bind M) q v S = ∫⁻ i, normalizedMeasure (M i) q v S ∂ν :=
  measure_bind_apply ν hM ((measurable_H q).div_const _ |>.ennreal_ofReal) v hS

theorem mixture_tail_bound {ι : Type*} [MeasurableSpace ι] {ν : Measure ι}
    [IsProbabilityMeasure ν] {M : ι → Measure Velocity} (hM : Measurable M)
    {q L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hc : ∀ᵐ i ∂ν, IsElementary L (M i))
    {v : Velocity} (hv : transverse v ≠ 0) (N : ℕ) :
    normalizedMeasure (ν.bind M) q v (tailRegion v N) ≤ tailBound q L N := by
  rw [normalized_bind_apply ν hM q v (measurableSet_tailRegion v N)]
  calc
    _ ≤ ∫⁻ _ : ι, tailBound q L N ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hc] with i hi
      obtain ⟨d, ρ, hd, hdmax, hprob, hρ, he⟩ := hi
      rw [he]
      exact normalized_tail_bound hq₁ hq₂ hd hdmax hv hρ N
    _ = _ := by simp

theorem dominated_tail_bound {ι : Type*} [MeasurableSpace ι] {ν : Measure ι}
    [IsProbabilityMeasure ν] {M : ι → Measure Velocity} (hM : Measurable M)
    {q L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hc : ∀ᵐ i ∂ν, IsElementary L (M i))
    {v : Velocity} (hv : transverse v ≠ 0) (N : ℕ)
    {c : Measure Velocity} {A : ℝ≥0∞} (hdom : c ≤ A • ν.bind M) :
    normalizedMeasure c q v (tailRegion v N) ≤ A * tailBound q L N := by
  have h := (measure_mono_incoming hdom (fun ξ => ENNReal.ofReal (H q ξ / H q v)) v)
    (tailRegion v N)
  rw [measure_smul, Measure.smul_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl (mixture_tail_bound hM hq₁ hq₂ hc hv N))

theorem measurableSet_axialRegion (v : Velocity) (a b : ℝ) :
    MeasurableSet (axialRegion v a b) :=
  measurableSet_Ioc.preimage (measurable_axial.comp (measurable_point v))

/-- The elementary modulus works without change for every probability mixture. -/
theorem mixture_axial_modulus {q L ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a b : ℝ), 0 < b - a → b - a ≤ δ →
      ∀ {ι : Type*} [MeasurableSpace ι] (ν : Measure ι) [IsProbabilityMeasure ν]
        (M : ι → Measure Velocity), Measurable M → (∀ᵐ i ∂ν, IsElementary L (M i)) →
        ∀ (v : Velocity), transverse v ≠ 0 →
          normalizedMeasure (ν.bind M) q v (axialRegion v a b) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hm⟩ := uniform_axial_modulus hq₁ hq₂ hε
  refine ⟨δ, hδ, ?_⟩
  intro a b hab hlen ι inst ν hprob M hM hc v hv
  rw [normalized_bind_apply ν hM q v (measurableSet_axialRegion v a b)]
  calc
    _ ≤ ∫⁻ _ : ι, ENNReal.ofReal ε ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hc] with i hi
      obtain ⟨d, ρ, hd, hdmax, hρprob, hρ, he⟩ := hi
      rw [he]
      exact hm a b hab hlen d ρ hρprob hd hdmax hρ v hv
    _ = _ := by simp

end BoltzmannNonuniqueness.SheetMixtures

end

end OAI
