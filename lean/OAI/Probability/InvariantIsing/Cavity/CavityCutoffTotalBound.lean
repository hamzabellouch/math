import OAI.Probability.InvariantIsing.Cavity.CavityRandomCutoff

namespace OAI

/-! The normalized cutoff is bounded also when its partition integral
is undefined: the existing zero convention then gives zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le_all {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (s : Set X) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  by_cases hi : Integrable (fun x => Real.exp (H x)) ν
  · exact cavity_cutoff_replica_abs_le ν H hi s (Set.to_countable s).measurableSet F hM hF
  · have hz : referencePartition ν H = 0 := integral_undef hi
    simp only [cavityCutoffReplicaMean, referenceReplicaMean, hz, zero_pow (by decide : 2 ≠ 0),
      div_zero, abs_zero]
    exact hM

end InvariantIsing

end

end OAI
