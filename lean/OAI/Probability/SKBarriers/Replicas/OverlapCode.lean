import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixReplicaBridge
import OAI.Probability.SKBarriers.Replicas.TriplePerturbation
import OAI.Probability.SKBarriers.Replicas.PairFactor

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def overlapCode {n : ℕ} (x y : Config n) : Fin (n+1) :=
  ⟨(Finset.univ.filter (fun i => x i=y i)).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans_eq (by simp))⟩

def codeOverlap (n : ℕ) (c : Fin (n+1)) : ℝ := (2*(c.val:ℝ)-(n:ℝ))/(n:ℝ)

theorem overlap_eq_codeOverlap {n : ℕ} (x y : Config n) :
    overlap x y=codeOverlap n (overlapCode x y) := by
  have he (i : Fin n) : spin (x i)*spin (y i)=2*(if x i=y i then (1:ℝ) else 0)-1 := by
    cases hx : x i <;> cases hy : y i <;> norm_num [spin]
  simp only [overlap,he,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  congr 1
  simp [overlapCode,Finset.sum_boole]

def pairReplicaCode {n : ℕ} (s : ReplicaConfig n 2) : Fin (n+1) := overlapCode (s 0) (s 1)

def tripleReplicaCode {n : ℕ} (s : ReplicaConfig n 3) : Fin 3 → Fin (n+1) :=
  ![overlapCode (s 0) (s 1),overlapCode (s 0) (s 2),overlapCode (s 1) (s 2)]

theorem replicaGram_pair {n : ℕ} (hn : 0 < n) (s : ReplicaConfig n 2) :
    replicaGram s=pairMatrix 1 (codeOverlap n (pairReplicaCode s)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [replicaGram,pairMatrix,pairReplicaCode,← overlap_eq_codeOverlap,overlap_comm,overlap_self hn]

theorem replicaGram_triple {n : ℕ} (hn : 0 < n) (s : ReplicaConfig n 3) :
    replicaGram s=tripleGram
      ((codeOverlap n (tripleReplicaCode s 0)+codeOverlap n (tripleReplicaCode s 1))/2)
      ((codeOverlap n (tripleReplicaCode s 0)-codeOverlap n (tripleReplicaCode s 1))/2)
      (codeOverlap n (tripleReplicaCode s 2)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [replicaGram,tripleGram,tripleReplicaCode,← overlap_eq_codeOverlap,overlap_comm,overlap_self hn] <;> ring_nf <;> exact overlap_comm _ _

theorem pairReplicaCode_gram {n : ℕ} (hn : 0 < n) {s t : ReplicaConfig n 2}
    (h : pairReplicaCode s=pairReplicaCode t) : replicaGram s=replicaGram t := by
  rw [replicaGram_pair hn,replicaGram_pair hn,h]

theorem tripleReplicaCode_gram {n : ℕ} (hn : 0 < n) {s t : ReplicaConfig n 3}
    (h : tripleReplicaCode s=tripleReplicaCode t) : replicaGram s=replicaGram t := by
  rw [replicaGram_triple hn,replicaGram_triple hn,h]

end SK.Analytic

end
end

end OAI
