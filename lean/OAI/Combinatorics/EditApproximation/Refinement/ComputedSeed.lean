import OAI.Combinatorics.EditApproximation.Coarse.CoarseParameters

namespace OAI

/-! Initial-seed bounds with computed numerical parameters. -/

namespace EditApproximation

open EditDistortion

theorem computed_initialSeed_bounds {α : Type*} [DecidableEq α]
    (N B D : ℕ) (x y : List α)
    (hB : B = (integerParameters N).B)
    (hD : D = computedCoarseDepth N (coarseEntryWidth x y))
    (hN : 0 < N) (hwidth : coarseEntryWidth x y ≤ N)
    (hell : 200 ≤ inputSmallLog N)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D)
    (hevent : CoarseInitialAccuracyEvent B D (initialThresholdQ N) (initialLambda N) x y draws) :
    edit x y ≤ coarseInitialValue B D (initialThresholdQ N) (initialLambda N) N x y draws ∧
      coarseInitialValue B D (initialThresholdQ N) (initialLambda N) N x y draws ≤
        (integerParameters N).initialFactor * edit x y := by
  have hH : (4 : ℚ) ≤ inputHeight N := by
    exact_mod_cast (computed_coarse_branching N hN hell).1
  have hden : (0 : ℚ) < 64 * (inputHeight N : ℚ) := by linarith
  have hlambda : initialLambda N < 1 := by
    unfold initialLambda
    exact (div_lt_one hden).2 (by linarith)
  have hcapacity : coarseEntryWidth x y ≤ B ^ D := by
    rw [hB, hD]
    exact (computed_coarse_depth N _ hN hwidth hell).1
  have hfactor : coarseStructuralFactor (initialLambda N) D ≤ 2 := by
    rw [hD]
    exact computed_coarse_structuralFactor N _ hN hwidth hell
  have hdistortion : 25 + 16 * B * D ≤ (integerParameters N).initialFactor := by
    rw [hB, hD]
    exact computed_coarse_distortion N _ hN hwidth hell
  have hbounds := coarseInitialValue_bounds B D (initialThresholdQ N) (initialLambda N)
    N x y draws hcapacity hwidth (pow_nonneg (Nat.cast_nonneg _) 4)
    (div_nonneg zero_le_one hden.le) hlambda hfactor hevent
  exact ⟨hbounds.1, hbounds.2.trans (Nat.mul_le_mul_right _ hdistortion)⟩

end EditApproximation

end OAI
