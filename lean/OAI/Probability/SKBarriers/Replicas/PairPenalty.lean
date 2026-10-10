import Mathlib
import OAI.Probability.SKBarriers.Replicas.PairFactor

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem finitePrefix_shared {n : ℕ} (a : ℕ) (v : Fin n → ℝ) (j : Fin n) (hj : j.val<a) :
    finitePrefix (fun l => if l.val<a then v l else 0) j=finitePrefix v j := by
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l ≤ j
  · have H : l.val<a := lt_of_le_of_lt hl hj
    simp only [ite_eq_left hl,ite_eq_left H]
  · simp only [ite_eq_right hl]

theorem splitPairFactor_penalty {k : ℕ} (a : ℕ) (m c : Fin (k+1) → ℝ) :
    let D := factorPath 2 2 k (splitPairFactor a c) (Fin.last k)
    matrixSquare 2 D-2*matrixInner 2 D D+
      (∑ j, zeroInitialAtoms k (splitPairMass a m) j*matrixSquare 2 (factorPath 2 2 k (splitPairFactor a c) j))=
      -2*∑ i : Fin k, m i.succ*((finitePrefix (fun l => (c l)^2) i.succ)^2-
        (finitePrefix (fun l => (c l)^2) i.castSucc)^2) := by
  dsimp only
  rw [matrixInner_self,zeroInitialAtoms_sum_mul_parts]
  have H (i : Fin k) :
      splitPairMass a m i.succ*(matrixSquare 2 (factorPath 2 2 k (splitPairFactor a c) i.succ)-
        matrixSquare 2 (factorPath 2 2 k (splitPairFactor a c) i.castSucc))=
      2*(m i.succ*((finitePrefix (fun l => (c l)^2) i.succ)^2-
        (finitePrefix (fun l => (c l)^2) i.castSucc)^2)) := by
    simp only [splitPairFactor_path,pairMatrix_square,splitPairMass]
    by_cases hi : i.succ.val<a
    · have hp : i.castSucc.val<a := by simpa only [Fin.val_castSucc] using Nat.lt_of_succ_lt hi
      rw [ite_eq_left hi,finitePrefix_shared a _ i.succ hi,finitePrefix_shared a _ i.castSucc hp]
      ring
    · have HP := finitePrefix_succ k (fun l => if l.val<a then (c l)^2 else 0) i
      rw [ite_eq_right hi,add_zero] at HP
      rw [ite_eq_right hi,HP]
      ring
  simp_rw [H]
  rw [← Finset.mul_sum]
  ring

theorem splitPairFactor_last {k : ℕ} (a : ℕ) (c : Fin (k+1) → ℝ) (hc : ∑ l, (c l)^2=1) :
    factorPath 2 2 k (splitPairFactor a c) (Fin.last k)=
      pairMatrix 1 (∑ l, if l.val<a then (c l)^2 else 0) := by
  rw [splitPairFactor_path,finitePrefix_last,finitePrefix_last,hc]

end SK.Analytic

end
end

end OAI
