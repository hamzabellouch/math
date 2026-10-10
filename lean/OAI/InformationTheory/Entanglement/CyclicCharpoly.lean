import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix Polynomial
namespace PencilCyclic
variable {K : Type*} [Field K] {n : ℕ}

def krylov (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => ((A ^ (j : ℕ)).mulVec v) i

lemma aeval_mulVec_eq {A : Matrix (Fin n) (Fin n) K} (v : Fin n → K)
    (q : K[X]) (hq : q.natDegree < n) :
    (aeval A q).mulVec v = (krylov A v).mulVec (fun i => q.coeff i) := by
  rw [Polynomial.aeval_eq_sum_range' hq]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, krylov, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.mulVec, dotProduct, mul_comm]

lemma polynomial_zero_of_cyclic {A B : Matrix (Fin n) (Fin n) K} {v : Fin n → K}
    (hB : B * krylov A v = 1) (q : K[X]) (hqn : q.natDegree < n)
    (hq : (aeval A q).mulVec v = 0) : q = 0 := by
  have hc : (fun i : Fin n => q.coeff i) = 0 := by
    have hh := congrArg (Matrix.mulVec B) hq
    rw [aeval_mulVec_eq v q hqn, Matrix.mulVec_mulVec, hB,
      Matrix.one_mulVec, Matrix.mulVec_zero] at hh
    exact hh
  ext k
  by_cases hk : k < n
  · exact congrFun hc ⟨k,hk⟩
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).trans (Polynomial.coeff_zero _).symm

lemma charpoly_eq_of_cyclic {A B : Matrix (Fin n) (Fin n) K} {v : Fin n → K}
    (hn : n ≠ 0) (hB : B * krylov A v = 1) (f : K[X]) (hf : f.Monic) (hfn : f.natDegree = n)
    (hfv : (aeval A f).mulVec v = 0) : A.charpoly = f := by
  have hdeg : (A.charpoly - f).natDegree < n := by
    exact Polynomial.IsMonicOfDegree.natDegree_sub_lt hn
      ⟨by simp, Matrix.charpoly_monic A⟩ ⟨hfn, hf⟩
  have he : (aeval A (A.charpoly - f)).mulVec v = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, zero_sub, Matrix.neg_mulVec, hfv, neg_zero]
  exact sub_eq_zero.mp (polynomial_zero_of_cyclic hB _ hdeg he)
end PencilCyclic

end

end OAI
