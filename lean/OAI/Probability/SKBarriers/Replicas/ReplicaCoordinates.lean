import Mathlib
import OAI.Probability.SKBarriers.Replicas.OverlapCode
import OAI.Probability.SKBarriers.Replicas.ReplicaFlip

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def tripleR {n : ℕ} (s : ReplicaConfig n 3) : ℝ := (overlap (s 0) (s 1)+overlap (s 0) (s 2))/2
def tripleDelta {n : ℕ} (s : ReplicaConfig n 3) : ℝ := (overlap (s 0) (s 1)-overlap (s 0) (s 2))/2
def tripleQ {n : ℕ} (s : ReplicaConfig n 3) : ℝ := overlap (s 1) (s 2)

theorem replicaGram_pair_overlap {n : ℕ} (hn : 0<n) (s : ReplicaConfig n 2) :
    replicaGram s=pairMatrix 1 (overlap (s 0) (s 1)) := by
  rw [replicaGram_pair hn]
  congr 1
  exact (overlap_eq_codeOverlap _ _).symm

theorem replicaGram_triple_overlap {n : ℕ} (hn : 0<n) (s : ReplicaConfig n 3) :
    replicaGram s=tripleGram (tripleR s) (tripleDelta s) (tripleQ s) := by
  simpa [tripleReplicaCode,← overlap_eq_codeOverlap,tripleR,tripleDelta,tripleQ] using
    replicaGram_triple hn s

theorem replicaGram_feasible {n d : ℕ} (s : ReplicaConfig n d) :
    Nonempty (MatrixStates n d (replicaGram s)) :=
  (matrixReplicaSet_nonempty_iff _).mp ⟨s,(mem_matrixReplicaSet _ _).mpr rfl⟩

@[simp] theorem tripleQ_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleQ (replicaFlip 0 s)=tripleQ s := by simp [tripleQ,replicaFlip]

@[simp] theorem tripleR_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleR (replicaFlip 0 s)= -tripleR s := by
  simp only [tripleR,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

@[simp] theorem tripleDelta_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleDelta (replicaFlip 0 s)= -tripleDelta s := by
  simp only [tripleDelta,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

theorem tripleRDelta_abs_le {n : ℕ} (s : ReplicaConfig n 3) {b : ℝ}
    (h₁ : |overlap (s 0) (s 1)|≤b) (h₂ : |overlap (s 0) (s 2)|≤b) :
    |tripleR s|≤b ∧ |tripleDelta s|≤b := by
  have H₁ := (abs_le.mp h₁)
  have H₂ := (abs_le.mp h₂)
  constructor <;> rw [abs_le] <;> dsimp only [tripleR,tripleDelta] <;> constructor <;> linarith

end SK.Analytic

end
end

end OAI
