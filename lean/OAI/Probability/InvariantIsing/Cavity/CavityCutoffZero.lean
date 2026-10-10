import OAI.Probability.InvariantIsing.Cavity.CavityCutoffSubtype

namespace OAI

/-! The cutoff/subtype identification also respects the zero convention
when the original reference gives the cutoff no mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_zero {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (hp : ν s = 0)
    (F : (Fin 2 → X) → ℝ) : cavityCutoffReplicaMean ν H s F = 0 := by
  let := isProbabilityMeasure_tilted hH
  have ht : (ν.tilted H) s = 0 := tilted_absolutelyContinuous ν H hp
  have hS : (Measure.pi (fun _ : Fin 2 => ν.tilted H)) (univ.pi (fun _ => s)) = 0 := by
    rw [Measure.pi_pi]
    simp [ht]
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F, ProbabilityTheory.cond, hS]
  simp

theorem cavity_cutoff_replica_subtype_all {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F = referenceReplicaMean (subtypeReference ν s)
      (fun x => H x) (fun σ => F (fun i => (σ i : X))) := by
  by_cases hp : ν s = 0
  · rw [cavity_cutoff_replica_zero ν H hH s hs hp F]
    simp [subtypeReference, hp, referenceReplicaMean, referencePartition]
  · exact cavity_cutoff_replica_eq_subtype ν H hH s hs hp F

end InvariantIsing

end

end OAI
