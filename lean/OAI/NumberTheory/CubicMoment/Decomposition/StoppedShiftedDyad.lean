import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDyadRestriction

namespace OAI

/-! The exact original-envelope sharp dyad as a smaller-envelope analytic
row, including the selected-bin and failed-prefix boundary shifts. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_shifted_sharp_dyad_to_row {ρ X F w Z Q : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (hXF : X ≤ F)
    (hw : 0 < w) (hZ : 2 ≤ Z) (W : ι → ℝ → ℂ) (z : ℝ)
    (j k h i : ℕ) (hk : 1 ≤ k) (early : Bool) (K : Eisenstein → ℂ)
    (hBX : stoppedNormDyadLength i ≤ X)
    (hj : geometricBinCount ρ F-geometricBinCount ρ X ≤ j)
    (hh : geometricBinCount ρ F-geometricBinCount ρ X ≤ h) :
    let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early)
    (∑ n ∈ stoppedNormDyad
        ((primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
          (fun n => Squarefree n ∧ norm n ≤ F)) i, β n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W
          (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
            (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n*K n := by
  dsimp only
  calc
    _ = ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W
          (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early) n*K n :=
      stoppedBeta_sharp_dyad_to_row hρ hρ₂ hX hXF hw hZ W z j k h i hk early K hBX
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [stoppedRowCoefficient_geometric_shift_of_bounds hρ (zero_lt_one.trans_le hX)
        hXF W w z 0 Z Q j k h early n hj hh]

end CubicFirstMoment

end

end OAI
