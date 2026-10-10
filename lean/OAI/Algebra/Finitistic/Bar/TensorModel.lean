import OAI.Algebra.Finitistic.Bar.Balanced
import OAI.Algebra.Finitistic.Bar.ChainSplitting

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

/-- The balanced free-tensor equivalence respects arbitrary A-linear maps, including bar faces. -/
theorem freeEquiv_natural (V W : Type u) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) :
    (Balanced.descend f W).comp (Balanced.map f (A ⊗[k] V) (A ⊗[k] W) h) =
      (FreeBaseChange.map f V W h).comp (Balanced.descend f V) := by
  apply (Balanced.relations f (A ⊗[k] V)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d z
  change d • FreeBaseChange.coefficient f W (h z) =
    FreeBaseChange.map f V W h (d • FreeBaseChange.coefficient f V z)
  rw [LinearMap.map_smul, FreeBaseChange.map_coefficient]

variable (k A D N : Type u) [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (f : A →ₐ[k] D)

/-- The actual balanced tensor of D with every term and differential of the verified bar resolution. -/
def tensorBarComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (Balanced.tensor f (term k A N (n+1))))
    (fun n => ModuleCat.ofHom (Balanced.map f _ _ (differential k A N (n+1))))
    (fun n => by
      apply ModuleCat.hom_ext
      change (Balanced.map f _ _ (differential k A N (n+1))).comp
        (Balanced.map f _ _ (differential k A N (n+1+1))) = 0
      rw [← Balanced.map_comp, differential_sq, Balanced.map_zero])

/-- The explicit two-sided bar is isomorphic to balanced tensor applied to a genuine projective resolution. -/
def tensorBarIso : tensorBarComplex k A D N f ≅ twoSidedComplex k A D N f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Balanced.freeEquiv f (term k A N n)).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      simp only [tensorBarComplex, twoSidedComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      exact (freeEquiv_natural f (term k A N (j+1)) (term k A N j)
        (differential k A N (j+1))).symm)

namespace SquareZero
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- The tensor of the actual free resolution splits by X-count as a D-module chain complex.
The identification of count r with the shifted r-fold derived tensor remains separate. -/
def tensorCountSplitting
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0) :
    tensorBarComplex k (TrivSqZeroExt D X) D N (fstHom k D X) ≅
      directSumComplex (twoSidedWeightComplex k D X N hN) :=
  tensorBarIso k (TrivSqZeroExt D X) D N (fstHom k D X) ≪≫
    (countSplitting k D X N hN).symm

end SquareZero
end DerivedBar

end

end OAI
