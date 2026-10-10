import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalBicomplex
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexSecondPageVanishing

namespace OAI

/-! # Rational homology of the finite total complex

Exact rationalization commutes with both homology directions, as well as the
actual total homology. Every finiteness hypothesis below is explicit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable (K : NatBicomplex)

def rationalRowHomologyComplexIso (j : ℕ) :
    rowHomologyComplex (rationalBicomplex K) j ≅
      ((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (rowHomologyComplex K j)) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => rationalModuleHomologyIso (K.X p) j) ?_
  intro p q hpq
  symm
  exact rationalModuleHomologyIso_naturality (K.d p q) j

def rationalBicomplexSecondPageIso (p j : ℕ) :
    (rowHomologyComplex (rationalBicomplex K) j).homology p ≅
      ModuleCat.of ℚ (ℚ ⊗[ℤ] (rowHomologyComplex K j).homology p) :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).mapIso
      (rationalRowHomologyComplexIso K j) ≪≫
    rationalModuleHomologyIso (rowHomologyComplex K j) p

def rationalBicomplexTotalHomologyIso (n : ℕ) :
    ((rationalBicomplex K).total (ComplexShape.down ℕ)).homology n ≅
      ModuleCat.of ℚ (ℚ ⊗[ℤ] (K.total (ComplexShape.down ℕ)).homology n) :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
      (rationalTotalComplexIso K).symm ≪≫
    rationalModuleHomologyIso (K.total (ComplexShape.down ℕ)) n

theorem rational_total_homology_finite_of_secondPage (n : ℕ)
    (hfin : ∀ p j, p + j = n →
      Module.Finite ℚ (ℚ ⊗[ℤ] (rowHomologyComplex K j).homology p)) :
    Module.Finite ℚ (ℚ ⊗[ℤ] (K.total (ComplexShape.down ℕ)).homology n) := by
  have hrow : ∀ p j, p + j = n →
      Module.Finite ℚ ((rowHomologyComplex (rationalBicomplex K) j).homology p) := by
    intro p j hpj
    let := hfin p j hpj
    exact Module.Finite.equiv (rationalBicomplexSecondPageIso K p j).symm.toLinearEquiv
  let : Module.Finite ℚ
      (((rationalBicomplex K).total (ComplexShape.down ℕ)).homology n) :=
    bicomplex_total_homology_finite_of_secondPage (rationalBicomplex K) n hrow
  exact Module.Finite.equiv (rationalBicomplexTotalHomologyIso K n).toLinearEquiv

theorem rational_total_homology_isZero_of_secondPage (n : ℕ)
    (hz : ∀ p j, p + j = n →
      Limits.IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] (rowHomologyComplex K j).homology p))) :
    Limits.IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] (K.total (ComplexShape.down ℕ)).homology n)) := by
  have hrow : ∀ p j, p + j = n →
      Limits.IsZero ((rowHomologyComplex (rationalBicomplex K) j).homology p) := by
    intro p j hpj
    exact (hz p j hpj).of_iso (rationalBicomplexSecondPageIso K p j)
  have ht := bicomplex_total_homology_isZero_of_secondPage (rationalBicomplex K) n hrow
  exact ht.of_iso (rationalBicomplexTotalHomologyIso K n).symm

end PolycyclicRecognition

end

end OAI
