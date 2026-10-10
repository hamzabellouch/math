import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalExtensionTotalHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalExtensionColumnHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexSecondPageFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NatTotalComplexSymmetry

namespace OAI

/-! # Integral homology finiteness for a normal extension

The criterion is proved using the actual bar bicomplex, its two homology
directions, and finite support elimination. No spectral-sequence convergence
is postulated. The finiteness hypotheses on quotient homology are explicit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem normalExtension_homology_finite_of_secondPage (n : ℕ)
    (hfin : ∀ i j, i + j = n →
      Module.Finite ℤ (groupHomology (normalDerivedHomology N i) j)) :
    Module.Finite ℤ (groupHomology (trivialIntegral G) n) := by
  classical
  let P := Rep.barResolution ℤ G
  let K := normalExtensionBicomplex N P
  have hrow : ∀ p j, p + j = n →
      Module.Finite ℤ ((rowHomologyComplex K.flip j).homology p) := by
    intro p j hpj
    let := hfin j p (by omega)
    exact Module.Finite.equiv (normalExtensionSecondPageIso N P j p).symm.toLinearEquiv
  let e := (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (K.totalFlipIso (ComplexShape.down ℕ)) ≪≫ normalExtensionTotalHomologyIso N P n
  let : Module.Finite ℤ ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).obj
      (K.flip.total (ComplexShape.down ℕ))) := by
    exact bicomplex_total_homology_finite_of_secondPage K.flip n hrow
  exact Module.Finite.equiv e.toLinearEquiv

end PolycyclicRecognition

end

end OAI
