import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockModules
import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductSplitting
import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalObjects

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BlockModule
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]

abbrev firstComplex (Z : CochainComplex (ModuleCat.{u} L) ℤ) :=
  ((ProductModules.firstInflation L R).mapHomologicalComplex (.up ℤ)).obj Z
abbrev secondComplex (Z : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ProductModules.secondInflation L R).mapHomologicalComplex (.up ℤ)).obj Z

variable {U V : Type u} [AddCommGroup U] [AddCommGroup V] [Module k U] [Module k V]

def firstMap [Module L U] [Module L V] (f : U →ₗ[L] V) : First k L R U →ₗ[L × R] First k L R V where
  __ := f.toAddHom
  map_smul' d x := f.map_smul d.1 x

def secondMap [Module R U] [Module R V] (f : U →ₗ[R] V) : Second k L R U →ₗ[L × R] Second k L R V where
  __ := f.toAddHom
  map_smul' d x := f.map_smul d.2 x
end LittleFinitistic.BlockModule
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)

theorem complex_d_all (n m : ℤ) : (complex k L R O T).d n m = objectMap k L R (O.d n m) (T.d n m) := by
  by_cases h : n+1=m
  · subst m
    rw [complex_d]
    rfl
  · have hh : ¬ (ComplexShape.up ℤ).Rel n m := h
    rw [(complex k L R O T).shape n m hh,O.shape n m hh,T.shape n m hh]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
