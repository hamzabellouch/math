import OAI.MeasureTheory.Falconer.Angular.SphereNormalization
import OAI.MeasureTheory.Falconer.Estimates.TroublesomePair

namespace OAI

/-! # Sphere-valued original radial laws, with a harmless diagonal value -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def originalRadialSphereLaw (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) : Measure (Sphere d) :=
  Measure.map (fun x => normalizeToSphere w₀ (x-z)) (ν.restrict {x | (z,x) ∈ G})

instance originalRadialSphereLaw_finite (w₀ : Sphere d) (ν : Measure (Space d))
    [IsFiniteMeasure ν] (G : Set (Space d × Space d)) (z : Space d) :
    IsFiniteMeasure (originalRadialSphereLaw w₀ ν G z) := by
  unfold originalRadialSphereLaw
  infer_instance

theorem originalRadialSphereLaw_apply (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (B : Set (Sphere d)) (hB : MeasurableSet B) :
    originalRadialSphereLaw w₀ ν G z B =
      ν {x | (z,x) ∈ G ∧ normalizeToSphere w₀ (x-z) ∈ B} := by
  have hm : Measurable (fun x : Space d => normalizeToSphere w₀ (x-z)) :=
    (normalizeToSphere_measurable w₀).comp (measurable_id.sub measurable_const)
  rw [originalRadialSphereLaw,Measure.map_apply hm hB,Measure.restrict_apply (hB.preimage hm)]
  congr 1
  ext x
  exact and_comm

theorem originalRadialSphereLaw_mass_le (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) :
    originalRadialSphereLaw w₀ ν G z Set.univ ≤ ν Set.univ := by
  rw [originalRadialSphereLaw_apply w₀ ν G z Set.univ MeasurableSet.univ]
  exact measure_mono (subset_univ _)

end Falconer

end OAI
