import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import OAI.Analysis.Laughlin.Fock.Hamiltonian

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators ComplexOrder
open Matrix

theorem occupationInner_star (Q : ℕ) (x y : Space Q) :
    star (occupationInner Q x y) = occupationInner Q y x := by
  simp [occupationInner,star_mul,mul_comm]

theorem create_annihilate_adjoint_right (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q x (create i y) = occupationInner Q (annihilate i x) y := by
  have h := congrArg star (create_annihilate_adjoint Q i y x)
  simpa only [occupationInner_star] using h

theorem pairCreate_pair_adjoint_right (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y : Space Q) :
    occupationInner Q x (pairCreateEnd Q c y) = occupationInner Q (pairEnd Q c x) y := by
  have h := congrArg star (pairCreate_pair_adjoint Q c y x)
  simpa only [occupationInner_star] using h

noncomputable def operatorLift {I : Type*} [Fintype I] (Q : ℕ)
    (plus minus : I → Module.End ℂ (Space Q)) (M : Matrix I I ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, M i j • (plus i * minus j)

theorem operatorLift_quadratic {I : Type*} [Fintype I] (Q : ℕ)
    (plus minus : I → Module.End ℂ (Space Q)) (M : Matrix I I ℂ)
    (ha : ∀ i x y, occupationInner Q x (plus i y) = occupationInner Q (minus i x) y)
    (x : Space Q) :
    occupationInner Q x (operatorLift Q plus minus M x) =
      ∑ A : Finset (Fin (Q+1)), star (fun i => (occupationBasis Q).repr (minus i x) A) ⬝ᵥ
        (M *ᵥ (fun i => (occupationBasis Q).repr (minus i x) A)) := by
  simp only [operatorLift,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    occupationInner_sum_right,occupationInner_smul_right,ha]
  simp only [occupationInner, dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro A hA
  ring

theorem operatorLift_positive {I : Type*} [Fintype I] (Q : ℕ)
    (plus minus : I → Module.End ℂ (Space Q)) (M : Matrix I I ℂ)
    (ha : ∀ i x y, occupationInner Q x (plus i y) = occupationInner Q (minus i x) y)
    (hM : M.PosSemidef) (x : Space Q) :
    0 ≤ (occupationInner Q x (operatorLift Q plus minus M x)).re := by
  rw [operatorLift_quadratic Q plus minus M ha x, Complex.re_sum]
  exact Finset.sum_nonneg (fun A hA =>
    (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg _)).1)

noncomputable def sourceFourCreateEnd (Q p : ℕ) (j k : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  sourcePairCreateEnd Q p * create j * create k

theorem sourceFour_adjoint_right (Q p : ℕ) (j k : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q x (sourceFourCreateEnd Q p j k y) =
      occupationInner Q (sourceFourEnd Q p j k x) y := by
  simp only [sourceFourCreateEnd,sourceFourEnd,sourcePairCreateEnd,sourcePairEnd,
    Module.End.mul_apply,pairCreate_pair_adjoint_right,create_annihilate_adjoint_right]

theorem sourceFourLift_positive {I : Type*} [Fintype I] (Q : ℕ)
    (p : I → ℕ) (j k : I → Fin (Q+1)) (M : Matrix I I ℂ) (hM : M.PosSemidef)
    (x : Space Q) :
    0 ≤ (occupationInner Q x (operatorLift Q
      (fun a => sourceFourCreateEnd Q (p a) (j a) (k a))
      (fun a => sourceFourEnd Q (p a) (j a) (k a)) M x)).re :=
  operatorLift_positive Q _ _ M (fun a => sourceFour_adjoint_right Q (p a) (j a) (k a)) hM x

end Laughlin.Fock

end OAI
