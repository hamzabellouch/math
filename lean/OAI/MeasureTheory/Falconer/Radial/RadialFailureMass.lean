import OAI.MeasureTheory.Falconer.Radial.RadialCapMass
import OAI.MeasureTheory.Falconer.Measures.TotalVariation
import OAI.MeasureTheory.Falconer.Measures.DistanceMeasure

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

@[fun_prop] theorem measurable_sourceRadialUnit_joint :
    Measurable (fun z : Plane × Plane => sourceRadialUnit z.1 z.2) := by
  apply Measurable.subtype_mk
  change Measurable (fun z : Plane × Plane => sourceRadialVector z.1 z.2)
  unfold sourceRadialVector
  apply Measurable.ite (isClosed_eq continuous_snd continuous_fst).measurableSet measurable_const
  fun_prop

noncomputable def radialFailure (S : Plane → Set UnitCircle) : Set (Plane × Plane) :=
  {z | sourceRadialUnit z.1 z.2 ∈ S z.1}

theorem measurableSet_radialFailure (S : Plane → Set UnitCircle)
    (hS : MeasurableSet {z : Plane × UnitCircle | z.2 ∈ S z.1}) :
    MeasurableSet (radialFailure S) :=
  hS.preimage (measurable_fst.prodMk measurable_sourceRadialUnit_joint)

theorem radial_failure_mass_le (μ ν : ProbabilityMeasure Plane)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K w : ℝ≥0∞} (hK : K ≠ ∞)
    (hN : ∀ᵐ x ∂(μ : Measure Plane), sourceDensityNorm p ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (S : Plane → Set UnitCircle)
    (hS : MeasurableSet {z : Plane × UnitCircle | z.2 ∈ S z.1})
    (hSw : ∀ᵐ x ∂(μ : Measure Plane), sourceArcLength (S x) ≤ w) :
    ((μ : Measure Plane).prod ν) (radialFailure S) ≤ K*w^(1-1/p) := by
  rw [Measure.prod_apply (measurableSet_radialFailure S hS)]
  calc
    (∫⁻ x, (ν : Measure Plane) (Prod.mk x ⁻¹' radialFailure S) ∂(μ : Measure Plane)) ≤
        ∫⁻ _, K*w^(1-1/p) ∂(μ : Measure Plane) := by
      apply lintegral_mono_ae
      filter_upwards [hN, hSw] with x hx hw
      have hSx : MeasurableSet (S x) := hS.preimage (measurable_const.prodMk measurable_id)
      exact radial_cap_mass_bound ν x hpq hK hx (S x) hSx hw
    _ = _ := by simp

instance weightedDistance_finite (π : Measure (Plane × Plane))
    [IsFiniteMeasure (π.withDensity distanceWeight)] : IsFiniteMeasure (weightedDistance π) := by
  unfold weightedDistance
  infer_instance

theorem radial_mask_totalVariation_bound (μ ν : ProbabilityMeasure Plane)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K w C : ℝ≥0∞} (hK : K ≠ ∞)
    (hN : ∀ᵐ x ∂(μ : Measure Plane), sourceDensityNorm p ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (S : Plane → Set UnitCircle)
    (hS : MeasurableSet {z : Plane × UnitCircle | z.2 ∈ S z.1})
    (hSw : ∀ᵐ x ∂(μ : Measure Plane), sourceArcLength (S x) ≤ w)
    (m : Plane × Plane → ℝ≥0∞) (hm : Measurable m) (hm1 : ∀ z, m z ≤ 1)
    [IsFiniteMeasure (((μ : Measure Plane).prod ν).withDensity distanceWeight)]
    (hbound : ∀ᵐ z ∂(μ : Measure Plane).prod ν, distanceWeight z ≤ C)
    (hout : ∀ᵐ z ∂(μ : Measure Plane).prod ν, z ∉ radialFailure S → m z = 1) :
    ∃ (σ ρ : Measure ℝ) (_hσ : IsFiniteMeasure σ) (_hρ : IsFiniteMeasure ρ),
      σ = (((μ : Measure Plane).prod ν).withDensity (fun z => distanceWeight z*m z)).map
        (fun z => dist z.1 z.2) ∧
      ρ = (((μ : Measure Plane).prod ν).withDensity (fun z => distanceWeight z*(1-m z))).map
        (fun z => dist z.1 z.2) ∧
      ((weightedDistance ((μ : Measure Plane).prod ν)).toSignedMeasure-σ.toSignedMeasure).totalVariation univ
        ≤ C*(K*w^(1-1/p)) := by
  have hw : Measurable distanceWeight := by unfold distanceWeight; fun_prop
  obtain ⟨σ, ρ, hσ, hρ, heσ, heρ, hb⟩ := masked_totalVariation_bound
    ((μ : Measure Plane).prod ν) (fun z => dist z.1 z.2) (by fun_prop)
    distanceWeight m hw hm hm1 (radialFailure S) C hbound hout
  exact ⟨σ, ρ, hσ, hρ, heσ, heρ, hb.trans
    (mul_le_mul_right (radial_failure_mass_le μ ν hpq hK hN S hS hSw) C)⟩

end PlanarFalconer

end OAI
