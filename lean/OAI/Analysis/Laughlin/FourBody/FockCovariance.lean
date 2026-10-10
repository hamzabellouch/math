import OAI.Analysis.Laughlin.Exterior.FourConjugation
import OAI.Analysis.Laughlin.FourBody.GroupIntertwining
import OAI.Analysis.Laughlin.Pair.FockHaar

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix Kronecker

theorem antisymmetric_exterior_sum (Q : ℕ) (f : SpinIndex Q Q → Space Q)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (a : SpinIndex Q Q → ℂ) :
    (∑ i, a i • f i) = ∑ i : WedgePairIndex Q, (a i.val-a i.val.swap) • f i.val := by
  apply (occupationBasis Q).repr.injective
  ext A
  have h := antisymmetric_ordered_sum Q
    (fun i => (occupationBasis Q).repr (f i) A) a (by
      intro i j; rw [hf,map_neg]; rfl)
  simpa only [map_sum,map_smul,Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,mul_comm] using h

noncomputable def wedgePairVector (Q : ℕ) (i : WedgePairIndex Q) : Space Q :=
  create i.val.1 (create i.val.2 1)

theorem wedgePairVector_rotation (Q : ℕ) (g : SourceSU2) (i : WedgePairIndex Q) :
    exteriorRotation Q g (wedgePairVector Q i) =
      ∑ j, wedgePairRepresentation Q g j i • wedgePairVector Q j := by
  have ha (i j : Fin (Q+1)) : create j (create i (1 : Space Q)) = -create i (create j 1) := by
    have h := LinearMap.congr_fun (create_anticommute j i) (1 : Space Q)
    exact eq_neg_of_add_eq_zero_left h
  rw [wedgePairVector,exteriorRotation_pair_basis]
  have h := antisymmetric_exterior_sum Q
    (fun k : SpinIndex Q Q => create k.1 (create k.2 (1 : Space Q))) ha
    (fun j : SpinIndex Q Q => sourceSpinRepresentation Q g j.1 i.val.1 *
      sourceSpinRepresentation Q g j.2 i.val.2)
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  change (_ - _) • wedgePairVector Q j = _ • wedgePairVector Q j
  congr 1
  dsimp [wedgePairRepresentation,wedgePairMatrix]
  ring

noncomputable def sourceFourVector (Q : ℕ) (i : FourWedgeIndex Q) : Space Q :=
  sourcePairVector Q i.1.val * wedgePairVector Q i.2

noncomputable def sourceFourFamilyEnd (Q : ℕ) (i : FourWedgeIndex Q) : Module.End ℂ (Space Q) :=
  sourceFourEnd Q i.1.val i.2.val.1 i.2.val.2

theorem sourceFourVector_adjoint (Q : ℕ) (i : FourWedgeIndex Q) (x y : Space Q) :
    occupationInner Q (sourceFourVector Q i*x) y =
      occupationInner Q x (sourceFourFamilyEnd Q i y) := by
  have he : sourceFourVector Q i*x = sourcePairVector Q i.1.val *
      create i.2.val.1 (create i.2.val.2 x) := by
    change (sourcePairVector Q i.1.val *
      (ExteriorAlgebra.ι ℂ (mode i.2.val.1)*(ExteriorAlgebra.ι ℂ (mode i.2.val.2)*1)))*x =
      sourcePairVector Q i.1.val *
        (ExteriorAlgebra.ι ℂ (mode i.2.val.1)*(ExteriorAlgebra.ι ℂ (mode i.2.val.2)*x))
    simp only [mul_one,mul_assoc]
  rw [he,sourcePairVector_adjoint,create_annihilate_adjoint,create_annihilate_adjoint]
  rfl

theorem sourceFourVector_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) (i : FourWedgeIndex Q) :
    exteriorRotation Q g (sourceFourVector Q i) =
      ∑ j, fourBodySpinRepresentation Q g j i • sourceFourVector Q j := by
  rw [sourceFourVector,map_mul,sourcePairVector_rotation Q hQ,wedgePairVector_rotation]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Fintype.sum_prod_type,
    fourBodySpinRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,Matrix.kroneckerMap,
    Matrix.of_apply,sourceFourVector]
  rw [Finset.sum_comm]

theorem sourceFourFamilyEnd_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (i : FourWedgeIndex Q) (x : Space Q) :
    sourceFourFamilyEnd Q i (exteriorRotation Q g x) =
      ∑ j, fourBodySpinRepresentation Q g i j •
        exteriorRotation Q g (sourceFourFamilyEnd Q j x) :=
  exteriorFamily_contraction_rotation Q (fourBodySpinRepresentation Q)
    (fourBodySpinRepresentation_inv Q) (sourceFourVector Q) (sourceFourFamilyEnd Q)
    (sourceFourVector_adjoint Q) (sourceFourVector_rotation Q hQ) g i x

end Laughlin.Fock

end OAI
