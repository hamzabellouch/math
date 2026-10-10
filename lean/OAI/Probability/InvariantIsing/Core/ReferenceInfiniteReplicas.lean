import OAI.Probability.InvariantIsing.Arrays.TensorLabeledTerminal

namespace OAI

/-! The finite reference replica mean as the initial coordinates of iid Gibbs replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma referenceReplicaMean_infinite {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (D : (Fin r → X) → ℝ) (hD : Measurable D) :
    referenceReplicaMean ν H D =
      ∫ σ : ℕ → X, D (fun i => σ i) ∂Measure.infinitePi (fun _ : ℕ => gibbsProbability ν H) := by
  let := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he]
  simp_rw [gibbsProbability_eq_tilted ν H he]
  have hp : MeasurePreserving (fun σ : ℕ → X => fun i : Fin r => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν.tilted H)) (Measure.pi (fun _ : Fin r => ν.tilted H)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]
  exact (hp.hasLaw.integral_comp hD.aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
