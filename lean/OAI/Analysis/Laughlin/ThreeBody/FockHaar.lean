import OAI.Analysis.Laughlin.Pair.FockHaar
import OAI.Analysis.Laughlin.ThreeBody.HaarNormalization

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix Kronecker

noncomputable def sourceThreeEnd (Q : ℕ) (i : PairOrbitalIndex Q) : Module.End ℂ (Space Q) :=
  annihilate i.2 * sourcePairEnd Q i.1.val

noncomputable def sourceThreeVector (Q : ℕ) (i : PairOrbitalIndex Q) : Space Q :=
  sourcePairVector Q i.1.val * create i.2 (1 : Space Q)

theorem sourceThreeVector_adjoint (Q : ℕ) (i : PairOrbitalIndex Q) (x y : Space Q) :
    occupationInner Q (sourceThreeVector Q i*x) y =
      occupationInner Q x (sourceThreeEnd Q i y) := by
  have he : sourceThreeVector Q i*x = sourcePairVector Q i.1.val * create i.2 x := by
    change (sourcePairVector Q i.1.val * (ExteriorAlgebra.ι ℂ (mode i.2)*1))*x =
      sourcePairVector Q i.1.val * (ExteriorAlgebra.ι ℂ (mode i.2)*x)
    simp only [mul_one,mul_assoc]
  rw [he,sourcePairVector_adjoint,create_annihilate_adjoint]
  rfl

theorem sourceThreeEnd_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (i : PairOrbitalIndex Q) (x : Space Q) :
    sourceThreeEnd Q i (exteriorRotation Q g x) =
      ∑ j, threeBodySpinRepresentation Q g i j • exteriorRotation Q g (sourceThreeEnd Q j x) := by
  simp only [sourceThreeEnd,Module.End.mul_apply,sourcePairEnd_rotation Q hQ g,
    map_sum,map_smul,annihilate_exteriorRotation,Finset.smul_sum,smul_smul]
  simp only [threeBodySpinRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,
    Matrix.kroneckerMap,Matrix.of_apply,Fintype.sum_prod_type]

theorem physical_threeBody_Fock_haar (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      ∑ z : Fin (Q+1),
        ((physicalThreeBodyTraceFormula Q z.val : ℂ)/(coupledWeight Q z.val+1 : ℕ)) *
          contractionForm Q (sourceThreeEnd Q)
            ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x := by
  rw [contractionForm_haar Q (threeBodySpinRepresentation Q)
    (threeBodySpinRepresentation_inv Q) (threeBodySpinRepresentation_continuous Q)
    _ (sourceThreeEnd_rotation Q (by omega)),physical_threeBody_certificate_haar Q hQ,
    contractionForm_sum]
  simp only [contractionForm_smul]

end Laughlin.Fock

end OAI
