import Mathlib.Tactic.Module
import OAI.Analysis.Laughlin.Fock.PairNormalization

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_vacuum {Q : ℕ} (a i : Fin (Q+1)) :
    annihilate a (create i (1 : Space Q)) = delta a i • (1 : Space Q) := by
  have h := LinearMap.congr_fun (mixed_car a i) (1 : Space Q)
  by_cases ha : a = i <;> simpa [Module.End.mul_apply,annihilate_vacuum,delta,ha] using h

theorem two_annihilate_three_create {Q : ℕ} (a b i j k : Fin (Q+1)) :
    annihilate b (annihilate a (create i (create j (create k (1 : Space Q))))) =
      (delta a i*delta b j-delta b i*delta a j) • create k (1 : Space Q) -
      (delta a i*delta b k-delta b i*delta a k) • create j (1 : Space Q) +
      (delta a j*delta b k-delta b j*delta a k) • create i (1 : Space Q) := by
  have h := LinearMap.congr_fun (normal_order_four a b i j) (create k (1 : Space Q))
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,Module.End.one_apply,annihilate_create_vacuum,map_smul,
    annihilate_vacuum,smul_zero,map_zero,add_zero,smul_smul] at h
  rw [h]
  module

theorem pairEnd_three_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i j k : Fin (Q+1)) :
    pairEnd Q c (create i (create j (create k (1 : Space Q)))) =
      (c i j-c j i) • create k (1 : Space Q) -
      (c i k-c k i) • create j (1 : Space Q) +
      (c j k-c k j) • create i (1 : Space Q) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    two_annihilate_three_create,smul_add,smul_sub,smul_smul]
  simp [delta,mul_sub,sub_smul,mul_ite,ite_smul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]

end Laughlin.Fock

end OAI
