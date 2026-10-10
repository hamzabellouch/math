import OAI.Analysis.KadisonKastler.CyclicFactorModules
import OAI.Analysis.KadisonKastler.WeakRowFactorization

namespace OAI

/-! Each member of a weak row-orbit closure has a unique bounded right
operator after compression to the left generated space. -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem hasFixedCyclicFactorization
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (F : BoundedWeakAlgebraMap M c)
    (hF : ∀ a, (F.map a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R)) :
    HasFixedRowFactorization (cyclicFactorRepresentation π L) (cyclicFactorLeft π L) ‖R‖ F :=
  ⟨cyclicFactorRight π L R, cyclicFactorRight_norm_le π L R,
    fun a => (hF a).trans (cyclicFactorization_eq π L R a).symm⟩

theorem exists_unique_cyclic_factor_of_mem_orbitClosure
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (F : BoundedWeakAlgebraMap M c)
    (hF : ∀ a, (F.map a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    {G : BoundedWeakAlgebraMap M c} (hG : G ∈ closure (boundedWeakRowOrbit F)) :
    ∃! S : H →L[ℂ] factorizationCyclicSpace π L, ‖S‖ ≤ ‖R‖ ∧
      ∀ a, (G.map a : H →L[ℂ] H) = (cyclicFactorLeft π L).adjoint.comp
        ((cyclicFactorRepresentation π L a).comp S) := by
  obtain ⟨S, hS, hs⟩ := hasFixedRowFactorization_of_mem_orbitClosure
    (cyclicFactorRepresentation π L) (cyclicFactorLeft π L) (norm_nonneg R)
    (hasFixedCyclicFactorization π L R F hF) hG
  refine ⟨S, ⟨hS, hs⟩, ?_⟩
  intro T hT
  exact cyclicFactorRight_unique π L T S (fun a => (hT.2 a).symm.trans (hs a))

theorem cyclic_right_factor_row_average
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (R S : H →L[ℂ] factorizationCyclicSpace π L)
    (F : Algebra M →ₗ[ℂ] Algebra M)
    (hF : ∀ a, (F a : H →L[ℂ] H) = (cyclicFactorLeft π L).adjoint.comp
      ((cyclicFactorRepresentation π L a).comp R))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (hS : ∀ a, (finiteRightAverage r F a : H →L[ℂ] H) =
      (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp S)) :
    S = representationRowAverage (cyclicFactorRepresentation π L) r R := by
  apply cyclicFactorRight_unique π L
  intro a
  exact (hS a).symm.trans
    (finiteRightAverage_operator_factorization F (cyclicFactorRepresentation π L)
      (cyclicFactorLeft π L) R hF r a)

end

end KadisonKastler

end OAI
