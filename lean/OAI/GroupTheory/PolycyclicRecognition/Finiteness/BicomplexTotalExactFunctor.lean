import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexDiagonalNaturality
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace OAI

/-! # Exactness of first-quadrant totalization

Finite antidiagonal coordinates transfer degreewise exactness to the actual
total-complex functor.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open Finset.HasAntidiagonal
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

abbrev integralFirstQuadrantTotal :=
  HomologicalComplex₂.totalFunctor (ModuleCat.{0} ℤ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)

instance integralFirstQuadrantTotal_additive : integralFirstQuadrantTotal.Additive where
  map_add := by
    intro K L f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (K.total (ComplexShape.down ℕ)).X n at x
    apply (bicomplexDiagonalEquiv L n).injective
    change bicomplexToDiagonal L n
        (((HomologicalComplex₂.total.map (f + g) (ComplexShape.down ℕ)).f n).hom x) =
      bicomplexToDiagonal L n
        ((((HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n).hom x) +
          (((HomologicalComplex₂.total.map g (ComplexShape.down ℕ)).f n).hom x))
    rw [bicomplexToDiagonal_natural, map_add,
      bicomplexToDiagonal_natural, bicomplexToDiagonal_natural]
    ext p
    rfl

theorem bicomplex_total_preserves_exact (S : ShortComplex NatBicomplex) (hs : S.Exact) :
    (S.map integralFirstQuadrantTotal).Exact := by
  apply HomologicalComplex.exact_of_degreewise_exact
  intro n
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change (S.X₂.total (ComplexShape.down ℕ)).X n at x
  change ((HomologicalComplex₂.total.map S.g (ComplexShape.down ℕ)).f n).hom x = 0 at hx
  have hg : bicomplexDiagonalMap S.g n (bicomplexToDiagonal S.X₂ n x) = 0 := by
    rw [← bicomplexToDiagonal_natural, hx, map_zero]
  have hlift : ∀ p : ↥(antidiagonal n), ∃ y : (S.X₁.X p.1.1).X p.1.2,
      ((S.f.f p.1.1).f p.1.2).hom y = bicomplexToDiagonal S.X₂ n x p := by
    intro p
    have h₁ := hs.map (HomologicalComplex.eval _ _ p.1.1)
    have h₂ := h₁.map (HomologicalComplex.eval _ _ p.1.2)
    apply (ShortComplex.moduleCat_exact_iff _).mp h₂
    exact congrFun hg p
  choose y hy using hlift
  refine ⟨bicomplexFromDiagonal S.X₁ n y, ?_⟩
  apply (bicomplexDiagonalEquiv S.X₂ n).injective
  change bicomplexToDiagonal S.X₂ n
    (((HomologicalComplex₂.total.map S.f (ComplexShape.down ℕ)).f n).hom
      (bicomplexFromDiagonal S.X₁ n y)) = _
  rw [bicomplexToDiagonal_natural, bicomplexToFromDiagonal]
  exact funext hy

instance integralFirstQuadrantTotal_preservesHomology :
    integralFirstQuadrantTotal.PreservesHomology :=
  ((Functor.exact_tfae integralFirstQuadrantTotal).out 2 3).mp
    bicomplex_total_preserves_exact

end PolycyclicRecognition

end

end OAI
