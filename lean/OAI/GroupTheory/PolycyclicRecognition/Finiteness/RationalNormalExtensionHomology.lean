import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalBicomplexHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalExtensionHomologyVanishing

namespace OAI

/-! # Rational homology comparison for the actual normal extension

These results apply exact rationalization to the constructed bar bicomplex.
They retain all second-page hypotheses and do not infer finite rational rank
from finite generation over the quotient group ring.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem normalExtension_rational_homology_finite_of_secondPage (n : ℕ)
    (hfin : ∀ i j, i + j = n →
      Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (normalDerivedHomology N i) j)) :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral G) n) := by
  classical
  let P := Rep.barResolution ℤ G
  let K := normalExtensionBicomplex N P
  have hrow : ∀ p j, p + j = n →
      Module.Finite ℚ (ℚ ⊗[ℤ] (rowHomologyComplex K.flip j).homology p) := by
    intro p j hpj
    let : Module.Finite ℚ
        (rationalModuleFunctor.obj (groupHomology (normalDerivedHomology N j) p)) := by
      exact hfin j p (by omega)
    exact Module.Finite.equiv
      (rationalModuleFunctor.mapIso (normalExtensionSecondPageIso N P j p)).symm.toLinearEquiv
  let e := rationalModuleFunctor.mapIso
    ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (K.totalFlipIso (ComplexShape.down ℕ)) ≪≫ normalExtensionTotalHomologyIso N P n)
  let : Module.Finite ℚ (rationalModuleFunctor.obj
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
        (K.flip.total (ComplexShape.down ℕ)))) := by
    exact rational_total_homology_finite_of_secondPage K.flip n hrow
  exact Module.Finite.equiv e.toLinearEquiv

theorem normalExtension_rational_homology_isZero_of_secondPage (n : ℕ)
    (hz : ∀ i j, i + j = n →
      Limits.IsZero (ModuleCat.of ℚ
        (ℚ ⊗[ℤ] groupHomology (normalDerivedHomology N i) j))) :
    Limits.IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral G) n)) := by
  classical
  let P := Rep.barResolution ℤ G
  let K := normalExtensionBicomplex N P
  have hrow : ∀ p j, p + j = n →
      Limits.IsZero (ModuleCat.of ℚ
        (ℚ ⊗[ℤ] (rowHomologyComplex K.flip j).homology p)) := by
    intro p j hpj
    exact (hz j p (by omega)).of_iso
      (rationalModuleFunctor.mapIso (normalExtensionSecondPageIso N P j p))
  have ht := rational_total_homology_isZero_of_secondPage K.flip n hrow
  let e := rationalModuleFunctor.mapIso
    ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (K.totalFlipIso (ComplexShape.down ℕ)) ≪≫ normalExtensionTotalHomologyIso N P n)
  exact ht.of_iso e.symm

theorem normalExtension_rational_homology_isZero_above (a b : ℕ)
    (hz : ∀ i j, a < i ∨ b < j →
      Limits.IsZero (ModuleCat.of ℚ
        (ℚ ⊗[ℤ] groupHomology (normalDerivedHomology N i) j)))
    (n : ℕ) (hn : a + b < n) :
    Limits.IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology (trivialIntegral G) n)) := by
  apply normalExtension_rational_homology_isZero_of_secondPage N n
  intro i j hij
  exact hz i j (by omega)

end PolycyclicRecognition

end

end OAI
