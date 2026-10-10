import OAI.Analysis.Laughlin.ThreeBody.PairAction

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairEnd_create_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i j : Fin (Q+1)) :
    pairEnd Q c * create i * create j =
      (c i j-c j i) • (1 : Module.End ℂ (Space Q)) -
      (∑ b, (c i b-c b i) • (create j * annihilate b)) +
      (∑ b, (c j b-c b j) • (create i * annihilate b)) +
      create i * create j * pairEnd Q c := by
  classical
  simp only [pairEnd,Finset.sum_mul,smul_mul_assoc,normal_order_four,
    smul_add,smul_sub,smul_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [delta,mul_ite,mul_one,mul_zero,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.mul_sum,mul_smul_comm]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,mul_assoc]
  have hs (a b : ℂ) (v : Module.End ℂ (Space Q)) : (a-b) • v = a • v-b • v := by
    apply LinearMap.ext
    intro x
    exact sub_smul a b (v x)
  simp only [hs,Finset.sum_sub_distrib]
  module

theorem pairEnd_annihilate_commute (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i : Fin (Q+1)) : pairEnd Q c * annihilate i = annihilate i * pairEnd Q c := by
  have h (a b : Fin (Q+1)) : annihilate b * annihilate a * annihilate i =
      annihilate i * (annihilate b * annihilate a) := by
    calc
      _ = annihilate b * (annihilate a * annihilate i) := mul_assoc _ _ _
      _ = annihilate b * -(annihilate i * annihilate a) := by rw [eq_neg_of_add_eq_zero_left (annihilate_anticommute a i)]
      _ = -(annihilate b * (annihilate i * annihilate a)) := by
        apply LinearMap.ext
        intro x
        exact map_neg (annihilate b) ((annihilate i * annihilate a) x)
      _ = -((annihilate b * annihilate i) * annihilate a) := by rw [mul_assoc]
      _ = -(-(annihilate i * annihilate b) * annihilate a) := by rw [eq_neg_of_add_eq_zero_left (annihilate_anticommute b i)]
      _ = _ := by
        apply LinearMap.ext
        intro x
        change -(-(annihilate i (annihilate b (annihilate a x)))) = _
        exact neg_neg _
  simp only [pairEnd,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,h]

theorem pairEnd_commute (Q : ℕ) (c d : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairEnd Q c * pairEnd Q d = pairEnd Q d * pairEnd Q c := by
  conv_lhs => arg 2; unfold pairEnd
  conv_rhs => arg 1; unfold pairEnd
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ← mul_assoc,pairEnd_annihilate_commute]
  simp only [mul_assoc,pairEnd_annihilate_commute]

end Laughlin.Fock

end OAI
