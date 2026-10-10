import OAI.Probability.DilutedSpin.AveragedEnergyRoot
import OAI.Probability.DilutedSpin.PhysicalInsertionEnergy

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p : ℕ}

lemma reservoirInsertion_energy (M : Model p) (C H : ℝ) (hH : 0≤H) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) {D : ℝ}
    (hf : ∀ i y a,|Real.log (dictionaryFactor (observableAt direction N) (observableAt anchor N) u i y a)|≤D)
    (b : ℕ) (F : (Fin b → Spin) → ℝ) :
    reservoirInsertion M C H N L u b F=
      (FiniteLaw.uniform : FiniteLaw (Fin b → Site N)).expect (fun i =>
        ∫ E,averagedEnergyRoot M.field.toMeasure (markLaw (weights L) N) (scoreRate N)
            (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (clipReal H)
            (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
            (E+(fun σ => F (fun j => readSpin σ (i j))))-
          averagedEnergyRoot M.field.toMeasure (markLaw (weights L) N) (scoreRate N)
            (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (clipReal H)
            (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) E
          ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
            (Measure.map (boundedPotential C) (bondLaw M N))) := by
  unfold reservoirInsertion reservoirLaw physicalBase physicalSpin
  exact fullRoot_sameInsertion_energy M.field.toMeasure (bondLaw M N) (markLaw (weights L) N)
    (reservoirRate M.alpha (p-1) N) (scoreRate N) (boundedPotential C)
    (Measurable.of_eval (measurable_boundedPotential C)) _ (gridExponents L)
    (gridExponents_pos L) (clipReal H) (measurable_clipReal H) _
    (fun y => clipReal_bound hH y) hf b F

end DilutedSpinGlass.UniversalDictionary

end

end OAI
