import OAI.Algebra.Finitistic.Bar.Splitting

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u

/-- The direct sum of module chain complexes, with the componentwise actual differential. -/
def directSumComplex {R : Type u} [Ring R] (C : ℕ → ChainComplex (ModuleCat R) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⨁ r, (C r).X n))
    (fun n => ModuleCat.ofHom (DirectSum.lmap (fun r => ((C r).d (n+1) n).hom)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply DFinsupp.ext
      intro r
      exact LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp ((C r).d_comp_d (n+1+1) (n+1) n)) (z r))

namespace SquareZero
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

/-- Chain-level count splitting of the actual two-sided absolute bar complex.
This is the first chain isomorphism in the proof of manuscript prop:bar-splitting.
Identification of these summands with derived tensor iterates is a separate dependency. -/
def countSplitting :
    directSumComplex (twoSidedWeightComplex k D X N hN) ≅
      twoSidedComplex k (TrivSqZeroExt D X) D N (fstHom k D X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (twoSidedWeightEquiv k D X N n).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply DirectSum.linearMap_ext
      intro r
      apply LinearMap.ext
      intro v
      simp only [directSumComplex, twoSidedComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, twoSidedWeightEquiv]
      change twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) j
          (DirectSum.coeLinearMap (twoSidedWeight k D X N (j+1))
            (DirectSum.lof D ℕ _ r v)) =
        DirectSum.coeLinearMap (twoSidedWeight k D X N j)
          (DirectSum.lmap (fun r => ((twoSidedWeightComplex k D X N hN r).d (j+1) j).hom)
            (DirectSum.lof D ℕ _ r v))
      rw [DirectSum.lmap_lof]
      erw [DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof]
      simp only [twoSidedWeightComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
      rfl)
end SquareZero
end DerivedBar

end

end OAI
