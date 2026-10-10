import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalCoefficientHomology

namespace OAI

/-! # Rationally zero coefficients have rationally zero homology

The proof uses the actual tensor-coinvariant terms of the bar complex. It
requires no finite-generation assumption on the group or the coefficients.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G]

theorem rational_tensor_isZero (A B : Type) [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (hA : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] A))) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] (A ⊗[ℤ] B))) := by
  let : Subsingleton (ℚ ⊗[ℤ] A) := ModuleCat.subsingleton_of_isZero hA
  have hs : Subsingleton ((ℚ ⊗[ℤ] A) ⊗[ℤ] B) := by
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
    | add x y hx hy => simp only [hx, hy, add_zero]
  let := hs
  let : Subsingleton (ℚ ⊗[ℤ] (A ⊗[ℤ] B)) :=
    (TensorProduct.assoc ℤ ℚ A B).symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem rational_coinvariants_isZero (A : Rep ℤ G)
    (hA : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] A))) :
    IsZero (rationalModuleFunctor.obj ((Rep.coinvariantsFunctor ℤ G).obj A)) := by
  let f := rationalModuleFunctor.map ((Rep.coinvariantsMk ℤ G).app A)
  exact IsZero.of_epi f hA

theorem rational_coinvariantsTensor_isZero (A B : Rep ℤ G)
    (hA : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] A))) :
    IsZero (rationalModuleFunctor.obj (((Rep.coinvariantsTensor ℤ G).obj A).obj B)) := by
  apply rational_coinvariants_isZero
  exact rational_tensor_isZero A B hA

theorem rational_homology_isZero_of_term (C : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (i : ℕ) (hC : IsZero (rationalModuleFunctor.obj (C.X i))) :
    IsZero (rationalModuleFunctor.obj (C.homology i)) := by
  let D := (rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  have hD : IsZero (D.homology i) := by
    apply ExactAt.isZero_homology
    apply ShortComplex.exact_of_isZero_X₂
    exact hC
  exact hD.of_iso (rationalModuleHomologyIso C i).symm

theorem rational_groupHomology_isZero_of_coefficient (A : Rep ℤ G)
    (hA : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] A))) (i : ℕ) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i)) := by
  classical
  let P := Rep.barResolution ℤ G
  let C := P.complex.coinvariantsTensorObj A
  have ht : IsZero (rationalModuleFunctor.obj (C.X i)) :=
    rational_coinvariantsTensor_isZero A _ hA
  exact (rational_homology_isZero_of_term C i ht).of_iso
    (rationalModuleFunctor.mapIso (groupHomologyIso A i P))

end PolycyclicRecognition

end

end OAI
