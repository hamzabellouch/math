import OAI.Probability.InvariantIsing.Fields.VectorTerminalTransition

namespace OAI

/-! Removing the first level preserves every later conditional ancestor kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma vectorTerminalBackward_shift (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (i : ℕ) :
    vectorTerminalBackward N (n+1) b v F (i+1) =
      vectorTerminalBackward N n (fun j => b (j+1)) (fun j => v (j+1)) F i := by
  simp only [vectorTerminalBackward,backwardValue,Nat.add_sub_add_right]
  congr 1 <;> simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma vectorTerminalAncestorKernel_shift (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    vectorTerminalAncestorKernel N (n+1) b v F hF (i+1) =
      vectorTerminalAncestorKernel N n (fun j => b (j+1)) (fun j => v (j+1)) F hF i := by
  ext z : 1
  change Measure.withDensity _ _ = Measure.withDensity _ _
  congr 1
  funext a
  simp only [vectorTerminalMultiplier,vectorTerminalUpdate,stoppedUpdate,
    Nat.add_lt_add_iff_right,vectorTerminalBackward_shift]

lemma vectorTerminalBackward_one (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) :
    vectorTerminalBackward N (n+1) b v F 1 =
      cascadeRecursion n (fun i => b (i+1)) (fun i => vectorGaussianLaw N (v (i+1)))
        (fun _ p => p.1+p.2) F := by
  simp only [vectorTerminalBackward,backwardValue,Nat.add_sub_cancel,Nat.add_comm 1]

end InvariantIsing

end

end OAI
