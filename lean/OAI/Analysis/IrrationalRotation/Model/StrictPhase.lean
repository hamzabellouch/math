import OAI.Analysis.IrrationalRotation.Model.PhaseFailure

namespace OAI

namespace Invariant233.ProductPhases

noncomputable def strictPhaseGoodCount {ι : Type*} (J : Finset ι) (b : ℝ)
    (k : ℤ) (θ : ι → ℝ) : ℕ := by
  classical
  exact (J.filter (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈
    Set.Ioo b (1 - b))).card

noncomputable def strictLargePhaseFailure {ι : Type*} (J : Finset ι) (N : ℝ) :
    Set (ι → ℝ) :=
  {θ | ∃ k ∈ largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card)),
    (strictPhaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ) <
      (J.card : ℝ) / 20}

def strictLargePhaseCondition {ι : Type*} (J : Finset ι) (N : ℝ) (θ : ι → ℝ) : Prop :=
  ∀ k : ℤ, N / 4 ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ (J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card) →
    (J.card : ℝ) / 20 ≤
      (strictPhaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ)

end Invariant233.ProductPhases

end OAI
