import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularEvaluationKernel

namespace OAI

/-! # Naturality of regular evaluation in the coefficient representation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep ℤ G}

theorem regularCoefficientAction_naturality (f : A ⟶ B) (q : ℤ[G]) (a : A) :
    regularCoefficientAction B q (f.hom a) = f.hom (regularCoefficientAction A q a) := by
  induction q using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.of_apply, regularCoefficientAction_single, one_smul]
    exact (Rep.hom_comm_apply f g⁻¹ a).symm
  | add q r hq hr => simp only [map_add, LinearMap.add_apply, hq, hr]
  | smul r q hq =>
    simp only [map_smul]
    change r • regularCoefficientAction B q (f.hom a) =
      f.hom (r • regularCoefficientAction A q a)
    rw [hq]
    exact (map_zsmul f.hom r (regularCoefficientAction A q a)).symm

theorem regularDualEvaluation_coefficient (P : Rep ℤ G) (f : A ⟶ B) (a : A) (p : P) :
    regularDualEvaluation P B (f.hom a) p = regularDualEvaluation P A a p ≫ f := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro q
  exact regularCoefficientAction_naturality f (q.hom p) a

theorem regularCoinvariantEvaluation_coefficient (P : Rep ℤ G) (f : A ⟶ B)
    (x : ((Rep.coinvariantsTensor ℤ G).obj A).obj P) :
    regularCoinvariantEvaluation P B (((Rep.coinvariantsTensor ℤ G).map f).app P x) =
      regularCoinvariantEvaluation P A x ≫ f := by
  induction x using Representation.Coinvariants.induction_on with
  | h x =>
    induction x using TensorProduct.inductionOn with
    | tmul a p => exact regularDualEvaluation_coefficient P f a p
    | add x y hx hy => simp only [map_add, hx, hy, Preadditive.add_comp]

theorem regularKernelCokernelEquiv_π {P Q : Rep ℤ G} (d : P ⟶ Q) (A : Rep ℤ G)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q)
    (x : LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map d).hom) :
    cokernel.π (regularDualMap d) ≫ regularKernelCokernelEquiv d A hP hQ x =
      regularCoinvariantEvaluation P A x.val := by
  exact cokernel.π_desc _ _ _

theorem regularKernelCokernelEquiv_coefficient {P Q : Rep ℤ G} (d : P ⟶ Q)
    [Projective P] [Projective Q]
    (hP : IntegralRepresentationFinite G P) (hQ : IntegralRepresentationFinite G Q)
    (f : A ⟶ B)
    (x : LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj A).map d).hom)
    (y : LinearMap.ker (((Rep.coinvariantsTensor ℤ G).obj B).map d).hom)
    (hxy : y.val = ((Rep.coinvariantsTensor ℤ G).map f).app P x.val) :
    regularKernelCokernelEquiv d B hP hQ y = regularKernelCokernelEquiv d A hP hQ x ≫ f := by
  apply (cancel_epi (cokernel.π (regularDualMap d))).mp
  rw [regularKernelCokernelEquiv_π, ← Category.assoc, regularKernelCokernelEquiv_π,
    hxy, regularCoinvariantEvaluation_coefficient]

end PolycyclicRecognition

end

end OAI
