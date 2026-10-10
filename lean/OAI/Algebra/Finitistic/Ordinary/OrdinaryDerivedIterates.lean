import OAI.Algebra.Finitistic.Ordinary.OrdinarySourceDerivedComparison
import Mathlib.Logic.Function.Iterate

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable (b : ℤ) (hb : a+(l:ℤ)=b)
variable (hP : ∀ n : ℤ, n < a ∨ b < n → Limits.IsZero (P.X n))
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (AlgebraD k l B))]

/-- The actual ordinary square on every native derived object, using essential surjectivity of Q. -/
def derivedSquareObject (Y : DerivedCategory (ModuleCat.{u} B)) :
    (derivedTensor P a l).obj ((derivedTensor P a l).obj
      ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj Y)) ≅
    (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj
      ((shiftedDerivedTensor P b l).obj Y) :=
  let e := DerivedCategory.Q.objObjPreimageIso Y
  (derivedTensor P a l).mapIso ((derivedTensor P a l).mapIso
    ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).mapIso e.symm)) ≪≫
  derivedSquareComparison P a l b hb hP (DerivedCategory.Q.objPreimage Y) ≪≫
  (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).mapIso
    ((shiftedDerivedTensor P b l).mapIso e)

/-- Every even iterate is the first-block inflation of the corresponding actual P[b] tensor iterate. -/
def derivedEvenIterate (n : ℕ) (Y : DerivedCategory (ModuleCat.{u} B)) :
    ((derivedTensor P a l).obj)^[2*n]
      ((BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj Y) ≅
    (BlockModule.derivedFirst B (B ⊗[k] ChainAlgebra k l)).obj
      (((shiftedDerivedTensor P b l).obj)^[n] Y) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih =>
    have hn : 2*(n+1) = (2*n+1)+1 := by omega
    rw [hn,Function.iterate_succ_apply',Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact (derivedTensor P a l).mapIso ((derivedTensor P a l).mapIso ih) ≪≫
      derivedSquareObject P a l b hb hP (((shiftedDerivedTensor P b l).obj)^[n] Y)
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
