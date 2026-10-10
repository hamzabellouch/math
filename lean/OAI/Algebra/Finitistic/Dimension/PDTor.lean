import OAI.Algebra.Finitistic.Dimension.PDTensorFunctor
import OAI.Algebra.Finitistic.Dimension.PDMinimalResolution
import Mathlib.CategoryTheory.Abelian.LeftDerived

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Tor is the left derived functor of the actual balanced tensor functor. -/
abbrev Tor (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} k :=
  ((tensorFunctor k A U).leftDerived n).obj M

variable [FiniteDimensional k A] (M : PDMinimal.FiniteModule k A)

def model : ChainComplex (ModuleCat k) ℕ :=
  ((tensorFunctor k A U).mapHomologicalComplex _).obj (PDMinimal.complex M)

/-- The chosen minimal resolution computes this actual derived functor. -/
def torIsoModel (n : ℕ) : Tor (k := k) U M.cat n ≅ (model U M).homology n :=
  (PDMinimal.resolution M).isoLeftDerivedObj (tensorFunctor k A U) n

variable (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)

include hU in
/-- Minimality annihilates every tensor differential, including non-adjacent ones. -/
theorem model_d_zero (i j : ℕ) : (model U M).d i j = 0 := by
  change (tensorFunctor k A U).map ((PDMinimal.complex M).d i j) = 0
  by_cases h : i = j+1
  · subst i
    rw [PDMinimal.complex_d]
    apply ModuleCat.hom_ext
    exact @mapRight_radical_zero k A _ _ _ U _ _ _
      (ScalarModule k A (PDMinimal.term M (j+1)).cat)
      (ScalarModule k A (PDMinimal.term M j).cat)
      _ _ _ (scalarModuleTower k A (PDMinimal.term M (j+1)).cat)
      _ _ _ (scalarModuleTower k A (PDMinimal.term M j).cat)
      hU (PDMinimal.differential M j) (PDMinimal.differential_radical M j)
  · rw [(PDMinimal.complex M).shape i j (by change ¬ j+1=i; exact Ne.symm h)]
    exact Functor.map_zero _ _ _

/-- Homology of the tensor of a minimal resolution is its term, because all
its differentials have been proved zero. -/
def torIsoTerm (n : ℕ) : Tor (k := k) U M.cat n ≅
    (tensorFunctor k A U).obj (PDMinimal.term M n).cat :=
  torIsoModel U M n ≪≫
    (ShortComplex.LeftHomologyData.ofZeros ((model U M).sc n)
      (model_d_zero U M hU _ _) (model_d_zero U M hU _ _)).homologyIso
end LittleFinitistic.PDTensor

end

end OAI
