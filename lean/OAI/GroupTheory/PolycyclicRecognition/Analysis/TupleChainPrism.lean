import OAI.GroupTheory.PolycyclicRecognition.Algebra.TuplePrism
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.RepresentationTheory.Homological.Resolution

namespace OAI

/-! # The prism on free homogeneous chains

Linearization of the tuple homotopy gives the chain homotopy. The formulas
below identify its components with the alternating prism and boundary.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Simplicial
variable {A B R : Type} [CommRing R]

def tupleFreeSimplicial (R A : Type) [CommRing R] : SimplicialObject (ModuleCat R) :=
  tupleSimplicial A ⋙ ModuleCat.monoidAlgebraFree R

def tupleChainComplex (R A : Type) [CommRing R] : ChainComplex (ModuleCat R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (tupleFreeSimplicial R A)

def tupleChainMap (f : A → B) : tupleChainComplex R A ⟶ tupleChainComplex R B :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map
    (((SimplicialObject.whiskering Type (ModuleCat R)).obj
      (ModuleCat.monoidAlgebraFree R)).map (tupleSimplicialMap f))

def tupleChainPrism (f g : A → B) : Homotopy (tupleChainMap (R := R) f) (tupleChainMap g) :=
  ((tupleSimplicialHomotopy f g).whiskerRight (ModuleCat.monoidAlgebraFree R)).toChainHomotopy

@[simp] theorem tupleChainMap_single (f : A → B) (n : ℕ) (x : Fin (n + 1) → A) :
    (tupleChainMap (R := R) f).f n (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single (f ∘ x) 1 := by
  change MonoidAlgebra.mapDomainLinearMap R R (fun y => f ∘ y)
    (MonoidAlgebra.single x 1) = _
  exact MonoidAlgebra.mapDomainLinearMap_single _ _ _

theorem tupleChainComplex_boundary (n : ℕ) (x : Fin (n + 2) → A) :
    (tupleChainComplex R A).d (n + 1) n (MonoidAlgebra.single x 1) =
      ∑ i : Fin (n + 2), (-1 : R) ^ i.val • MonoidAlgebra.single (x ∘ i.succAbove) 1 := by
  change ((tupleChainComplex R A).d (n + 1) n).hom (MonoidAlgebra.single x 1) = _
  simp [tupleChainComplex, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    tupleFreeSimplicial, tupleSimplicial, SimplicialObject.δ, SimplexCategory.δ,
    Fin.succAboveOrderEmb, ModuleCat.monoidAlgebraFree, ← Int.cast_smul_eq_zsmul R]
  erw [LinearMap.sum_apply]
  simp

theorem tupleChainPrism_single (f g : A → B) (n : ℕ) (x : Fin (n + 1) → A) :
    (tupleChainPrism (R := R) f g).hom n (n + 1) (MonoidAlgebra.single x 1) =
      -∑ i : Fin (n + 1), (-1 : R) ^ i.val • MonoidAlgebra.single (tuplePrism f g i x) 1 := by
  change ((tupleChainPrism (R := R) f g).hom n (n + 1)).hom
    (MonoidAlgebra.single x 1) = _
  simp only [tupleChainPrism, SimplicialObject.Homotopy.toChainHomotopy,
    SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    SimplicialObject.Homotopy.whiskerRight, tupleSimplicialHomotopy,
    ModuleCat.monoidAlgebraFree]
  erw [ModuleCat.hom_neg, ModuleCat.hom_sum]
  erw [LinearMap.neg_apply, LinearMap.sum_apply]
  change -(∑ i : Fin (n + 1), ((-1 : ℤ) ^ i.val) •
    (MonoidAlgebra.mapDomainLinearMap R R (tuplePrism f g i)
      (MonoidAlgebra.single x 1))) = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [MonoidAlgebra.mapDomainLinearMap_single]
  simp [← Int.cast_smul_eq_zsmul R]

end PolycyclicRecognition

end

end OAI
