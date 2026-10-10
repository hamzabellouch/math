import OAI.NumberTheory.JointDickman.Arithmetic.OrderedSimplex

namespace OAI

/-! # Integrability of the least-coordinate slices -/
namespace JointDickman
open MeasureTheory Filter

 theorem orderedSimplexMass_succ_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (u : ℝ) :
    Integrable (fun s => orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s)) μ := by
  let E : Set (ℝ × (Fin n → ℝ)) :=
    (fun z => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) ⁻¹' orderedTupleRegion (n+1) u
  have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hE : MeasurableSet E := (orderedTupleRegion_measurable _ _).preimage hcons
  have he (s : ℝ) : orderedSimplexMass (μ.restrict (Set.Ioi s)) n (u-s) =
      (Measure.pi (fun _ : Fin n => μ)).real ((fun t => (s,t)) ⁻¹' E) := by
    unfold orderedSimplexMass
    rw [← Measure.restrict_pi_pi, measureReal_def,
      Measure.restrict_apply (orderedTupleRegion_measurable _ _)]
    congr 2
    ext t
    exact (orderedTupleRegion_cons n s u t).symm
  simp_rw [he]
  apply Integrable.of_bound (measurable_measure_prodMk_left hE).ennreal_toReal.aestronglyMeasurable
    ((Measure.pi (fun _ : Fin n => μ)).real Set.univ)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact measureReal_mono (Set.subset_univ _)

end JointDickman

end OAI
