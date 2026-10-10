import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RegularProjectiveEvaluation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CokernelHomModule

namespace OAI

/-! # The kernel comparison induced by regular evaluation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

private def regularEvaluationKernelAddEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q) :
    LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map f).hom ≃+
      LinearMap.ker (Linear.leftComp ℤ A (regularDualMap f)) where
  toFun x := ⟨regularCoinvariantEvaluation P A x, by
    change regularDualMap f ≫ regularCoinvariantEvaluation P A x.val = 0
    rw [← regularCoinvariantEvaluation_naturality, x.property, map_zero]⟩
  invFun y := ⟨(regularProjectiveEvaluationEquiv P A hP).symm y, by
    apply (regularCoinvariantEvaluation_bijective Q A hQ).1
    rw [map_zero, regularCoinvariantEvaluation_naturality]
    change regularDualMap f ≫ regularProjectiveEvaluationEquiv P A hP
      ((regularProjectiveEvaluationEquiv P A hP).symm y.val) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (regularProjectiveEvaluationEquiv P A hP).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    exact (regularProjectiveEvaluationEquiv P A hP).apply_symm_apply y.val
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _

def regularEvaluationKernelEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q) :
    LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map f).hom ≃ₗ[ℤ]
      LinearMap.ker (Linear.leftComp ℤ A (regularDualMap f)) where
  __ := regularEvaluationKernelAddEquiv f A hP hQ
  map_smul' r x := map_intCast_smul (regularEvaluationKernelAddEquiv f A hP hQ) ℤ ℤ r x

def regularKernelCokernelEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q) :
    LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map f).hom ≃ₗ[ℤ]
      (cokernel (regularDualMap f) ⟶ A) :=
  (regularEvaluationKernelEquiv f A hP hQ).trans
    (cokernelHomModuleEquiv (regularDualMap f) A).symm

end PolycyclicRecognition

end

end OAI
