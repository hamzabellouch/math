import OAI.Algebra.AuslanderReiten.Homology.DerivedSingle
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem concentratedNat_exact (K : ChainComplex C ℕ) (n : ℕ)
    (hex : ∀ m : ℕ, m ≠ n → K.ExactAt m) (i : ℤ) (hi : i ≠ -(n : ℤ)) :
    (K.extend ComplexShape.embeddingDownNat).ExactAt i := by
  by_cases hh : ∃ m : ℕ, -(m : ℤ) = i
  · obtain ⟨m, rfl⟩ := hh
    exact (K.extend_exactAt_iff ComplexShape.embeddingDownNat (j := m) rfl).mpr
      (hex m (by omega))
  · exact K.extend_exactAt ComplexShape.embeddingDownNat i (by intro m hm; exact hh ⟨m, hm⟩)

def concentratedNatDerivedIso [HasDerivedCategory C]
    (K : ChainComplex C ℕ) (n : ℕ) (X : C)
    (hex : ∀ m : ℕ, m ≠ n → K.ExactAt m) (e : K.homology n ≅ X) :
    DerivedCategory.Q.obj (K.extend ComplexShape.embeddingDownNat) ≅
      ((DerivedCategory.singleFunctor C 0).obj X)⟦(n : ℤ)⟧ :=
  derivedSingleIso _ (-(n : ℤ)) (concentratedNat_exact K n hex) ≪≫
    (DerivedCategory.singleFunctor C (-(n : ℤ))).mapIso
      (K.extendHomologyIso ComplexShape.embeddingDownNat (j := n) rfl ≪≫ e) ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).app X).symm

end ArExplicit

end

end OAI
