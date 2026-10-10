import OAI.Algebra.AuslanderReiten.Complete.FiniteCompleteResolution
import OAI.Algebra.AuslanderReiten.Basic

namespace OAI

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

theorem gorensteinProjective_of_totallyAcyclic
    (M : Type u) [AddCommGroup M] [Module R M]
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicComplex P)
    (e : M ≃ₗ[R] CompleteComparison.Cokernel P 0) : GorensteinProjective R M := by
  refine ⟨P, fun n => ⟨hP.finite n, hP.projective n⟩, hP.exactAt, ?_, ⟨e⟩⟩
  intro n f hf
  obtain ⟨g, hg⟩ := hP.dualExact n f hf
  exact ⟨g, hg.symm⟩

theorem FrobeniusTrace.finite_gorensteinProjective
    {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]
    (τ : FrobeniusTrace k R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] [Module.Finite k M] : GorensteinProjective R M := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_finite_complete_resolution k R τ M
  exact gorensteinProjective_of_totallyAcyclic M P hP e

end ArExplicit

end OAI
