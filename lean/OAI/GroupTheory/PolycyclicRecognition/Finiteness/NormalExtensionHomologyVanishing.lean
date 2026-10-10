import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalExtensionHomologyFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexSecondPageVanishing

namespace OAI

/-! # Homological vanishing for a normal extension

The explicit second-page comparison and the finite diagonal filtration give
the required additive bound for integral homology, with its hypotheses visible.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem normalExtension_homology_isZero_of_secondPage (n : ℕ)
    (hz : ∀ i j, i + j = n →
      Limits.IsZero (groupHomology (normalDerivedHomology N i) j)) :
    Limits.IsZero (groupHomology (trivialIntegral G) n) := by
  classical
  let P := Rep.barResolution ℤ G
  let K := normalExtensionBicomplex N P
  have hrow : ∀ p j, p + j = n →
      Limits.IsZero ((rowHomologyComplex K.flip j).homology p) := by
    intro p j hpj
    exact (hz j p (by omega)).of_iso (normalExtensionSecondPageIso N P j p)
  have ht := bicomplex_total_homology_isZero_of_secondPage K.flip n hrow
  let e := (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (K.totalFlipIso (ComplexShape.down ℕ)) ≪≫ normalExtensionTotalHomologyIso N P n
  exact ht.of_iso e.symm

theorem normalExtension_homology_isZero_above (a b : ℕ)
    (hz : ∀ i j, a < i ∨ b < j →
      Limits.IsZero (groupHomology (normalDerivedHomology N i) j))
    (n : ℕ) (hn : a + b < n) : Limits.IsZero (groupHomology (trivialIntegral G) n) := by
  apply normalExtension_homology_isZero_of_secondPage N n
  intro i j hij
  exact hz i j (by omega)

end PolycyclicRecognition

end

end OAI
