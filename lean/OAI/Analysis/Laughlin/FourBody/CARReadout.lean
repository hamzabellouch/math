import Mathlib.Tactic.Abel
import OAI.Analysis.Laughlin.Fock.PairNormalization

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_apply (Q : ℕ) (a b : Fin (Q+1)) (x : Space Q) :
    annihilate a (create b x) = delta a b • x - create b (annihilate a x) := by
  have h := LinearMap.congr_fun (annihilate_create a b) x
  simpa only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply] using h

theorem annihilate_three_create (Q : ℕ) (a x y z : Fin (Q+1)) :
    annihilate a (create x (create y (create z (1 : Space Q)))) =
      delta a x • create y (create z (1 : Space Q)) -
      delta a y • create x (create z (1 : Space Q)) +
      delta a z • create x (create y (1 : Space Q)) := by
  simp only [annihilate_create_apply,annihilate_vacuum,map_zero,sub_zero,map_sub,map_smul]
  abel

theorem annihilate_four_create (Q : ℕ) (a x y z w : Fin (Q+1)) :
    annihilate a (create x (create y (create z (create w (1 : Space Q))))) =
      delta a x • create y (create z (create w (1 : Space Q))) -
      delta a y • create x (create z (create w (1 : Space Q))) +
      delta a z • create x (create y (create w (1 : Space Q))) -
      delta a w • create x (create y (create z (1 : Space Q))) := by
  rw [annihilate_create_apply,annihilate_three_create]
  simp only [map_sub,map_add,map_smul]
  abel

theorem pairEnd_four_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y z w : Fin (Q+1)) :
    pairEnd Q c (create x (create y (create z (create w (1 : Space Q))))) =
      (c x y-c y x) • create z (create w (1 : Space Q)) -
      (c x z-c z x) • create y (create w (1 : Space Q)) +
      (c x w-c w x) • create y (create z (1 : Space Q)) +
      (c y z-c z y) • create x (create w (1 : Space Q)) -
      (c y w-c w y) • create x (create z (1 : Space Q)) +
      (c z w-c w z) • create x (create y (1 : Space Q)) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    annihilate_four_create,map_sub,map_add,map_smul,annihilate_three_create,
    smul_sub,smul_add,smul_smul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [delta,mul_ite,mul_one,mul_zero,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [sub_smul]
  abel

end Laughlin.Fock

end OAI
