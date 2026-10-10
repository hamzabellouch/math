import OAI.Algebra.Finitistic.Ordinary.OrdinaryComplexAction
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k : Type u} [Field k]

/-- The genuine cochain differential on the selected finite interval. -/
abbrev intervalTerms (P : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ) (l : ℕ)
    (i : Fin (l+1)) : Type u := P.X (a + (i.val : ℤ))

def intervalDifferential (P : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ) (l : ℕ)
    (i j : Fin (l+1)) : intervalTerms P a l i →ₗ[k] intervalTerms P a l j :=
  (P.d (a + (i.val : ℤ)) (a + (j.val : ℤ))).hom

theorem intervalDifferential_square (P : CochainComplex (ModuleCat.{u} k) ℤ)
    (a : ℤ) (l : ℕ) (i j h : Fin (l+1)) :
    (intervalDifferential P a l j h).comp (intervalDifferential P a l i j) = 0 := by
  have h := P.d_comp_d (a + (i.val : ℤ)) (a + (j.val : ℤ)) (a + (h.val : ℤ))
  exact congrArg (fun f => f.hom) h

/-- The ordinary C-module O formed from the actual terms and differential of P. -/
@[instance_reducible]
def cochainModule (P : CochainComplex (ModuleCat.{u} k) ℤ) (a : ℤ) (l : ℕ) :
    Module (ChainAlgebra k l) (OrdinaryTerms (intervalTerms P a l)) :=
  OrdinaryTerms.module _ (intervalDifferential P a l) (intervalDifferential_square P a l)
end LittleFinitistic.OrdinarySimulation

end

end OAI
