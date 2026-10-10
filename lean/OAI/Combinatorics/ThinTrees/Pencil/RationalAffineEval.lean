import Mathlib
import OAI.Combinatorics.ThinTrees.Pencil.AffinePencil

namespace OAI

/-! Rational affine eval. -/

section


namespace AlgorithmicThinTrees.RationalForms
open Matrix Finset
open scoped BigOperators
namespace Affine
variable {d : ℕ}
def rat (v : Fin d → ℚ) (a : Affine d) : ℚ := a.1+∑i,a.2 i*v i
@[simp] lemma rat_cst (v : Fin d → ℚ) (q : ℚ) : rat v (cst q)=q := by simp [rat,cst]
@[simp] lemma rat_coord (v : Fin d → ℚ) (i : Fin d) : rat v (coord i)=v i := by
  simp [rat,coord,Pi.single_apply,ite_mul]
@[simp] lemma rat_zero (v : Fin d → ℚ) : rat v (0 : Affine d)=0 := by simp [rat]
@[simp] lemma rat_add (v : Fin d → ℚ) (a b : Affine d) : rat v (a+b)=rat v a+rat v b := by
  simp [rat,add_mul,sum_add_distrib];ring
@[simp] lemma rat_sub (v : Fin d → ℚ) (a b : Affine d) : rat v (a-b)=rat v a-rat v b := by
  simp [rat,sub_mul,sum_sub_distrib];ring
@[simp] lemma rat_smul (v : Fin d → ℚ) (q : ℚ) (a : Affine d) : rat v (q • a)=q*rat v a := by
  simp [rat,mul_add,mul_assoc,mul_sum]
@[simp] lemma rat_sum {I : Type*} (s : Finset I) (f : I → Affine d) (v : Fin d → ℚ) :
    rat v (∑i ∈ s,f i)=∑i ∈ s,rat v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]
lemma cast_rat (v : Fin d → ℚ) (a : Affine d) :
    (rat v a : ℝ)=real (fun i => (v i:ℝ)) a := by simp [rat,real]
end Affine
lemma pencil_eval {d N : ℕ} (A : Matrix (Fin N) (Fin N) (Affine d)) (hA : A.IsSymm)
    (v : Fin d → ℚ) : (pencil A hA).eval v=A.map (Affine.rat v) := by
  ext i j
  simp only [CurrentKS.RationalSDP.Pencil.eval,pencil,Matrix.map_apply,Affine.rat]
  erw [Matrix.add_apply,Matrix.sum_apply]
  congr 1
  apply sum_congr rfl
  intro k _
  change v k * (A i j).2 k = (A i j).2 k * v k
  ring
end AlgorithmicThinTrees.RationalForms
end

end OAI
