import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveParameterSets
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_positive_parameter_sets_sequence {m : ℕ} {R : ℝ}
    (scale : ℕ → ℝ) (hR : 0 < R)
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ F : ℕ → Set (Fin m → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 R) ∧
      (∀ r, 0 < (volume (F r)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (F r)).toReal) ∧
      ∀ᶠ r in atTop, F r = E r := by
  classical
  let F := fun r => if 0 < (volume (E r)).toReal then E r else closedBall 0 R
  have heq : ∀ᶠ r in atTop, F r = E r :=
    hmlower.eventually_pos.mono (fun _ h => ite_eq_left h)
  have hball : 0 < (volume (closedBall (0 : Fin m → ℝ) R)).toReal := by
    rw [Real.volume_pi_closedBall _ hR.le, ENNReal.toReal_ofReal (by positivity)]
    positivity
  refine ⟨F, ?_, ?_, ?_, ?_, heq⟩
  · intro r
    dsimp [F]
    split_ifs
    · exact hE r
    · exact measurableSet_closedBall
  · intro r
    dsimp [F]
    split_ifs
    · exact hER r
    · exact Subset.rfl
  · intro r
    dsimp [F]
    split_ifs with h
    · exact h
    · exact hball
  · apply hmlower.mono
    exact heq.mono (fun _ h => le_of_eq (congrArg (fun s => (volume s).toReal) h.symm))

end PolycyclicRecognition

end

end OAI
