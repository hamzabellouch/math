import OAI.InformationTheory.QuantumCircuit.Circuit

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma tensorMatrix_smul {N : ℕ} (c : Fin N → ℝ) (a : Fin N → QubitOperator) :
    tensorMatrix (fun i => c i • a i) = (∏ i, c i) • tensorMatrix a := by
  ext x y
  simp only [tensorMatrix, Matrix.smul_apply, Complex.real_smul, Finset.prod_mul_distrib,
    Complex.ofReal_prod]

open scoped MatrixOrder in
lemma tensorMatrix_nonneg {N : ℕ} (a : Fin N → QubitOperator) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ tensorMatrix a := by
  choose b hb using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (ha i)
  have h : tensorMatrix a = star (tensorMatrix b) * tensorMatrix b := by
    rw [tensorMatrix_star, tensorMatrix_mul]
    congr 1
    funext i
    exact hb i
  rw [h]
  exact star_mul_self_nonneg _

open scoped MatrixOrder in
lemma tensorMatrix_le_one {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) : tensorMatrix a ≤ 1 := by
  classical
  have hsum := tensorMatrix_sum_patterns (Finset.univ : Finset (Fin N))
    (fun i => 1 - a i) a (fun _ => 1)
  simp only [Finset.mem_univ, ite_true, sub_add_cancel, tensorMatrix_one] at hsum
  rw [← hsum]
  have hmem : (∅ : Finset (Fin N)) ∈ Finset.univ.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  have h := Finset.single_le_sum (fun F (_ : F ∈ (Finset.univ : Finset (Fin N)).powerset) =>
    tensorMatrix_nonneg (fun i => if i ∈ F then 1 - a i else a i)
      (fun i => by split_ifs; exact sub_nonneg.mpr (ha1 i); exact ha i)) hmem
  simpa only [Finset.notMem_empty, ite_false] using h

def Count.empty {N : ℕ} : Count N where
  support := ∅
  vector := fun _ _ => 0
  normalized := by simp

@[simp] lemma Count.empty_zero {N : ℕ} : (Count.empty : Count N).zero = 1 := by
  simp [Count.zero, Count.empty]

def Count.join {N : ℕ} (A B : Count N) : Count N where
  support := A.support ∪ B.support
  vector i := if i ∈ A.support then A.vector i else B.vector i
  normalized i hi := by
    classical
    split_ifs with hA
    · exact A.normalized i hA
    · exact B.normalized i ((Finset.mem_union.mp hi).resolve_left hA)

lemma Count.join_zero {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    (A.join B).zero = A.zero * B.zero := by
  classical
  dsimp only [Count.zero, Count.join]
  rw [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hA : i ∈ A.support
  · have hB : i ∉ B.support := Finset.disjoint_left.mp h hA
    simp [hA, hB]
  · by_cases hB : i ∈ B.support <;> simp [hA, hB]

lemma Count.disjoint_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute A.zero B.zero := by
  classical
  show A.zero * B.zero = B.zero * A.zero
  dsimp only [Count.zero]
  rw [tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hA : i ∈ A.support
  · have hB : i ∉ B.support := Finset.disjoint_left.mp h hA
    simp [hA, hB]
  · simp [hA]

/-- Subcounts with the same axes, allowing repeated monomial indices to collapse. -/
def Count.restrict {N : ℕ} (M : Count N) (S : Finset (Fin N)) : Count N where
  support := M.support ∩ S
  vector := M.vector
  normalized i hi := M.normalized i (Finset.mem_inter.mp hi).1

lemma Count.restrict_zero_mul {N : ℕ} (M : Count N) (S T : Finset (Fin N)) :
    (M.restrict S).zero * (M.restrict T).zero = (M.restrict (S ∪ T)).zero := by
  classical
  dsimp only [Count.zero, Count.restrict]
  rw [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hi, hS, hT, (rankOne_projection (M.normalized i hi)).isIdempotentElem.eq]
  · simp [hi]

lemma Count.restrict_support_card {N : ℕ} (M : Count N) (S : Finset (Fin N)) :
    (M.restrict S).support.card ≤ S.card := Finset.card_le_card Finset.inter_subset_right

end QAC

end

end OAI
