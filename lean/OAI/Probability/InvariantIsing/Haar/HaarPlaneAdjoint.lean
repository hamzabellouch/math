import OAI.Probability.InvariantIsing.Haar.HaarPlaneFrame

namespace OAI

/-! Coefficients of the adjoint action in the redundant coordinate-plane frame. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_adjoint_expansion {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) (i j : Fin N) :
    A*planeGenerator i j-planeGenerator i j*A =
      (∑ k, A k i • planeGenerator k j)+(∑ k, A k j • planeGenerator i k) := by
  classical
  have hskew (k l : Fin N) : A k l = -A l k := congrFun (congrFun hA l) k
  ext k l
  simp only [planeGenerator,Matrix.mul_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    Matrix.sum_apply,Matrix.single_apply,smul_eq_mul,mul_sub,sub_mul,
    Finset.sum_sub_distrib]
  simp only [ite_and,mul_ite,ite_mul,mul_one,one_mul,mul_zero,zero_mul,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.sum_const_zero,Finset.mem_univ,ite_true]
  rw [hskew l i,hskew l j]
  split_ifs <;> ring

lemma sum_skew_symmetric_coeff {N : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A)
    (T : Fin N → Fin N → V) (hT : ∀ i j, T i j = T j i) :
    (∑ i, ∑ j, A i j • T i j) = 0 := by
  have hskew (i j : Fin N) : A j i = -A i j := congrFun (congrFun hA i) j
  have hs : (∑ i, ∑ j, A i j • T i j) = -(∑ i, ∑ j, A i j • T i j) := by
    calc
      (∑ i, ∑ j, A i j • T i j) = ∑ i, ∑ j, A j i • T j i := Finset.sum_comm
      _ = ∑ i, ∑ j, -(A i j • T i j) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hskew i j,hT j i,neg_smul]
      _ = -(∑ i, ∑ j, A i j • T i j) := by
        simp only [Finset.sum_neg_distrib]
  have hz : (2 : ℝ) • (∑ i, ∑ j, A i j • T i j) = 0 := by
    rw [two_smul]
    nth_rw 1 [hs]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end InvariantIsing

end

end OAI
