import OAI.Algebra.AuslanderReiten.Complete.FiniteCompleteResolution
import OAI.Algebra.AuslanderReiten.Cones.CochainCokernel
import Mathlib.Algebra.Homology.Embedding.Restriction

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace CompleteComparison

def cochainOfChain (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ := P.restriction negIndexEmbedding

def cochainOfChainCokernelEquiv (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    CochainCokernel (cochainOfChain P) ≃ₗ[R] Cokernel P 0 :=
  LinearEquiv.refl R _

theorem cochainOfChain_totallyAcyclic (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hP : TotallyAcyclicComplex P) : TotallyAcyclicCochain (cochainOfChain P) where
  finite i := hP.finite (-i)
  projective i := hP.projective (-i)
  exactAt i := by
    rw [(cochainOfChain P).exactAt_iff' (i := i - 1) (j := i) (k := i + 1)
      (by simp) (by simp), ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hP.exactAt_of_indices (by change -(i - 1) = -i + 1; omega)
      (by change -(i + 1) = -i - 1; omega)
  dualExact i := by
    exact hP.dualExact_of_indices (by change -(i - 1) = -i + 1; omega)
      (by change -(i + 1) = -i - 1; omega)

end CompleteComparison

namespace FiniteLeftModule

open CompleteComparison

variable {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]

noncomputable def completeCochain (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    CochainComplex (ModuleCat.{u} R) ℤ := cochainOfChain (M.completeComplex τ)

theorem completeCochain_totallyAcyclic (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    TotallyAcyclicCochain (M.completeCochain τ) :=
  cochainOfChain_totallyAcyclic _ (M.completeComplex_totallyAcyclic τ)

noncomputable def completeCochainCokernelEquiv (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    CochainCokernel (M.completeCochain τ) ≃ₗ[R] M.carrier :=
  (cochainOfChainCokernelEquiv (M.completeComplex τ)).trans (M.completeCokernelEquiv τ)

end FiniteLeftModule
end ArExplicit

end OAI
