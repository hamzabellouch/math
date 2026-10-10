import Mathlib
import OAI.Analysis.Commutator.BalancedDefect

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix CStarAlgebra ContinuousFunctionalCalculus

namespace Kadison.CStarBlock

variable {A : Type*}

local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

def block (a b c d : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix !![a,b;c,d]

@[simp] lemma block00 (a b c d : A) : block a b c d 0 0=a := rfl

@[simp] lemma block01 (a b c d : A) : block a b c d 0 1=b := rfl

@[simp] lemma block10 (a b c d : A) : block a b c d 1 0=c := rfl

@[simp] lemma block11 (a b c d : A) : block a b c d 1 1=d := rfl

variable [CStarAlgebra A]

lemma block_mul (a b c d e f g h : A) :
    block a b c d*block e f g h=block (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block,CStarMatrix.mul_apply,Fin.sum_univ_two]

lemma star_block (a b c d : A) : star (block a b c d)=block (star a) (star c) (star b) (star d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable [PartialOrder A] [StarOrderedRing A]

lemma diagonal_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (X : CStarMatrix ι ι A) (hX : 0≤X) (i : ι) : 0≤X i i := by
  classical
  let : ContinuousFunctionalCalculus ℂ (CStarMatrix ι ι A) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι A) := CStarAlgebra.instNonnegSpectrumClass
  let R := CFC.sqrt X
  have hR : star R*R=X := by rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq]; exact CFC.sqrt_mul_sqrt_self X hX
  rw [←hR,CStarMatrix.mul_apply]
  exact Finset.sum_nonneg (fun j _ => star_mul_self_nonneg (R j i))

lemma contraction_block_nonneg (x : A) (hx : ‖x‖≤1) : 0≤block 1 x (star x) 1 := by
  have hp : 0≤1-star x*x := by simpa only [star_star] using BalancedDilation.defect_nonneg (star x) (by simpa using hx)
  let r := CFC.sqrt (1-star x*x)
  have hr : star r=r := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  have hr2 : r*r=1-star x*x := CFC.sqrt_mul_sqrt_self _ hp
  have he : star (block 1 x 0 r)*block 1 x 0 r=block 1 x (star x) 1 := by
    rw [star_block,block_mul]
    simp [hr,hr2]
  rw [←he]
  exact star_mul_self_nonneg _

lemma contraction_of_block_nonneg (x : A) (hx : 0≤block 1 x (star x) 1) : ‖x‖≤1 := by
  let T := block (1:A) (-x) 0 1
  have hp : 0 ≤ star T*block 1 x (star x) 1*T := star_left_conjugate_nonneg hx T
  have he : star T*block 1 x (star x) 1*T=block 1 0 0 (1-star x*x) := by
    simp [T,star_block,block_mul,sub_eq_add_neg,add_comm]
  have hd : 0≤1-star x*x := by simpa only [he,block11] using diagonal_nonneg _ hp 1
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg (star x*x) (star_mul_self_nonneg x)).mpr (sub_nonneg.mp hd)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg x]

end Kadison.CStarBlock

end

end
end

end OAI
