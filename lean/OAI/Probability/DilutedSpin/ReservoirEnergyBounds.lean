import OAI.Probability.DilutedSpin.CavityAllocatedMean

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma reservoirEnergyRoot_lipschitz (M : Model p) {H : ℝ} (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) : LipschitzWith 1 (reservoirEnergyRoot M H N L u) :=
  averagedEnergyRoot_lipschitz M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
    _ (gridExponents L) (gridExponents_pos L) (clipReal H) (measurable_clipReal H)
    (locatedFactor (spinFactor direction anchor u)) (fun y => clipReal_bound hH y)
    (fun i _ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a)

lemma reservoirEnergyLaw_eq (M : Model p) (C : ℝ) :
    reservoirEnergyLaw M C N=compoundPoisson (reservoirRate M.alpha (p-1) N)
      (Measure.map (indexedPotential (N := N) (clipSample C))
        (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) := rfl

instance reservoirEnergyLaw_probability (M : Model p) (C : ℝ) :
    IsProbabilityMeasure (reservoirEnergyLaw M C N) := by
  rw [reservoirEnergyLaw_eq]
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) (clipSample C))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  infer_instance

lemma reservoirEnergyLaw_integrable (M : Model p) {C : ℝ} (hC : 0≤C) :
    Integrable id (reservoirEnergyLaw M C N) := by
  rw [reservoirEnergyLaw_eq]
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) (clipSample C))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply compoundPoisson_integrable_id
  exact integrable_indexedPotential M.disorder.toMeasure (clipSample C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)) hC
    (fun _ _ => clipReal_bound hC _)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
