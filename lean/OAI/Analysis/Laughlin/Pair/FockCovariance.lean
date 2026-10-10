import OAI.Analysis.Laughlin.Exterior.FamilyCovariance
import OAI.Analysis.Laughlin.Pair.ExteriorRotation

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourcePairCreateEnd_mul (Q p : ℕ) (x : Space Q) :
    sourcePairCreateEnd Q p x = sourcePairVector Q p*x := by
  simp only [sourcePairCreateEnd,pairCreateEnd,sourcePairVector,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,Finset.sum_mul,smul_mul_assoc,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*x) =
    (ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*1))*x
  simp only [mul_one,mul_assoc]

theorem sourcePairVector_adjoint (Q p : ℕ) (x y : Space Q) :
    occupationInner Q (sourcePairVector Q p*x) y = occupationInner Q x (sourcePairEnd Q p y) := by
  rw [← sourcePairCreateEnd_mul]
  exact pairCreate_pair_adjoint Q _ x y

theorem sourcePairEnd_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) (x : Space Q) :
    sourcePairEnd Q p.val (exteriorRotation Q g x) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g p q •
        exteriorRotation Q g (sourcePairEnd Q q.val x) := by
  exact exteriorFamily_contraction_rotation Q (sourceSpinRepresentation (2*Q-2))
    (sourceSpinRepresentation_inv (2*Q-2))
    (fun p : Fin (2*Q-2+1) => sourcePairVector Q p.val)
    (fun p => sourcePairEnd Q p.val)
    (fun p => sourcePairVector_adjoint Q p.val)
    (fun g p => sourcePairVector_rotation Q hQ g p) g p x

end Laughlin.Fock

end OAI
