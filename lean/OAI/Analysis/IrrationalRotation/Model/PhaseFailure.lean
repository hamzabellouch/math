import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval

namespace OAI

namespace Invariant233.ProductPhases

noncomputable def failureBound (m : ℝ) : ℝ :=
  2 * m ^ ((4 / 5 : ℝ) * m) * (2 : ℝ) ^ m *
    (10 * m ^ (-19 / 20 : ℝ)) ^ ((19 / 20 : ℝ) * m)

noncomputable def nonzeroIntegerWindow (R : ℝ) : Finset ℤ :=
  (Finset.Icc (-Int.floor R) (Int.floor R)).erase 0

noncomputable def largePhaseTimes (N R : ℝ) : Finset ℤ :=
  (nonzeroIntegerWindow R).filter (fun k => N / 4 ≤ |(k : ℝ)|)

noncomputable def phaseGoodCount {ι : Type*} (J : Finset ι) (b : ℝ)
    (k : ℤ) (θ : ι → ℝ) : ℕ := by
  classical
  exact (J.filter (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈
    Set.Icc b (1 - b))).card

noncomputable def largePhaseFailure {ι : Type*} (J : Finset ι) (N : ℝ) :
    Set (ι → ℝ) :=
  {θ | ∃ k ∈ largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card)),
    (phaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ) <
      (J.card : ℝ) / 20}

def largePhaseCondition {ι : Type*} (J : Finset ι) (N : ℝ) (θ : ι → ℝ) : Prop :=
  ∀ k : ℤ, N / 4 ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ (J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card) →
    (J.card : ℝ) / 20 ≤
      (phaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ)

def smallPhaseCondition {ι : Type*} (J : Finset ι) (K G : ℝ) (θ : ι → ℝ) : Prop :=
  ∀ k : ℤ, G * K ≤ |(k : ℝ)| → |(k : ℝ)| ≤ (J.card : ℝ) * K / 4 →
    ∀ i ∈ J, 1 - Int.fract ((k : ℝ) * θ i) ∈
      Set.Icc (G / J.card) (1 - G / J.card)

end Invariant233.ProductPhases

end OAI
