import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.RingTheory.Finiteness.Defs

namespace OAI

noncomputable section

/-!
# Quantitative renorming of real ℓ¹ with fixed vector-space operations
-/

open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

def HasBAP (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (Λ : ℝ) : Prop :=
  ∀ C : Set X, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ T : X →L[ℝ] X, Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧
      ‖T‖ ≤ Λ ∧ ∃ η : ℝ, η < ε ∧ ∀ u ∈ C, ‖T u - u‖ ≤ η

def blockBound (p : ℕ) : ℝ := 300 * (p : ℝ)^2 + 150 * (p : ℝ) + 5

open scoped BigOperators ENNReal

def RealL1 : Type := lp (fun _ : ℕ => ℝ) (1 : ENNReal)

noncomputable instance : NormedAddCommGroup RealL1 :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

noncomputable instance : NormedSpace ℝ RealL1 :=
  inferInstanceAs (NormedSpace ℝ (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

def RealL1RenormingStatement : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∃ N : AddGroupNorm RealL1,
    (∀ (r : ℝ) (c : RealL1), N (r • c) = |r| * N c) ∧
    (∀ c : RealL1, (1 / 2 : ℝ) * ‖c‖ ≤ N c ∧ N c ≤ blockBound p * ‖c‖) ∧
    (let m : Module ℝ RealL1 := inferInstance
     letI : NormedAddCommGroup RealL1 := N.toNormedAddCommGroup
     ∃ s : NormedSpace ℝ RealL1, s.toModule = m ∧
       letI := s
       CompleteSpace RealL1 ∧
       HasBAP RealL1 (2 * blockBound p) ∧ ¬ HasBAP RealL1 (p : ℝ) ∧
         (p = 1 → ¬ HasBAP RealL1 1))

theorem real_l1_quantitative_renorming : RealL1RenormingStatement := by
  sorry

end DiscreteFree

end

end OAI
