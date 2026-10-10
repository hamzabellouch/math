import OAI.Analysis.CircleDomains.Sobolev.ScalarFlatteningWeak

namespace OAI

/-! The flattening construction retains a genuine Sobolev witness. Its
squared gradient error is exactly the energy above the removed values. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem flattenValues_zero (O : Set ℝ) : flattenValues O 0 = 0 := by
  simp [flattenValues]

 theorem flattenValues_norm_le {O : Set ℝ} (hO : MeasurableSet O) (t : ℝ) :
    ‖flattenValues O t‖ ≤ ‖t‖ := by
  simpa only [flattenValues_zero, dist_zero_right, NNReal.coe_one, one_mul] using
    (flattenValues_lipschitz hO).dist_le_mul t 0

 theorem flattenValues_monotone {O : Set ℝ} (hO : MeasurableSet O) :
    Monotone (flattenValues O) := by
  intro a b hab
  have h := intervalIntegral.integral_nonneg_of_forall (μ := volume) (f := Oᶜ.indicator (fun _ => (1 : ℝ)))
    hab (fun t => by by_cases ht : t ∈ O <;> simp [ht])
  rw [← flattenValues_sub hO] at h
  linarith

 theorem flattenValues_unit_interval {O : Set ℝ} (hO : MeasurableSet O)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : flattenValues O t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simpa only [flattenValues_zero] using flattenValues_monotone hO ht.1
  · have h := flattenValues_norm_le hO t
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using h) |>.trans ht.2

 def flattenedGradient (O : Set ℝ) (u : EuclideanPlane → ℝ)
    (V : EuclideanPlane → EuclideanPlane) : EuclideanPlane → EuclideanPlane :=
  (u ⁻¹' Oᶜ).indicator V

 def flattenedSobolevWitness
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ p ∈ U, u p ∈ Icc (-B) B)
    {O : Set ℝ} (hO : IsOpen O) : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ u) U where
  memLp := W.memLp.norm.mono' ((flattenValues_lipschitz hO.measurableSet).continuous.comp hu).aestronglyMeasurable
    (Eventually.of_forall (fun p => by simpa only [Function.comp_apply, norm_norm] using flattenValues_norm_le hO.measurableSet (u p)))
  weakGrad := flattenedGradient O u W.weakGrad
  weakGrad_component_memLp := by
    intro i
    have he : (fun p => flattenedGradient O u W.weakGrad p i) =
        (u ⁻¹' Oᶜ).indicator (fun p => W.weakGrad p i) := by
      funext p
      by_cases hp : u p ∈ O <;> simp [flattenedGradient, hp]
    rw [he]
    exact (W.weakGrad_component_memLp i).indicator (hu.measurable hO.measurableSet.compl)
  isWeakGrad := by
    intro i
    have he : (fun p => flattenedGradient O u W.weakGrad p i) =
        (fun p => Oᶜ.indicator (fun _ => (1 : ℝ)) (u p)*W.weakGrad p i) := by
      funext p
      by_cases hp : u p ∈ O <;> simp [flattenedGradient, hp]
    rw [he]
    exact flattenValues_weak_partial hU hu W hB hb hO i

 theorem flattenValues_compact_support {u : EuclideanPlane → ℝ}
    (hu : HasCompactSupport u) (O : Set ℝ) : HasCompactSupport (flattenValues O ∘ u) :=
  hu.comp_left (flattenValues_zero O)

 theorem flattenedGradient_energy_error (E : Set EuclideanPlane)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (V : EuclideanPlane → EuclideanPlane)
    {O : Set ℝ} (hO : MeasurableSet O) :
    (∫⁻ p in E, ENNReal.ofReal (‖flattenedGradient O u V p - V p‖^2)) =
      scalarEnergyMeasure E u V O := by
  rw [scalarEnergyMeasure, Measure.map_apply hu.measurable hO,
    withDensity_apply _ (hu.measurable hO)]
  rw [← lintegral_indicator (hu.measurable hO)]
  apply lintegral_congr
  intro p
  by_cases hp : u p ∈ O <;> simp [flattenedGradient, hp]

end CircleDomainRigidity

end

end OAI
