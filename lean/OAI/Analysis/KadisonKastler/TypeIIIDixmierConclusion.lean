import OAI.Analysis.KadisonKastler.TypeIIIDixmier
import OAI.Analysis.KadisonKastler.SelfAdjointAveraging
import OAI.Analysis.KadisonKastler.ScalarOrbitClosure

namespace OAI

/-! # The exact Dixmier conclusion in represented type III factors -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H}

/-- Spectral matrices and two successive self-adjoint averages handle every
operator of the factor. -/
theorem TypeIIIFactor.exists_scalar_average (hM : TypeIIIFactor M)
    (x : Algebra M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply x.val - z • (1 : H →L[ℂ] H)‖ < ε :=
  exists_scalar_average_of_selfAdjoint hM.exists_selfAdjoint_scalar_average x ε hε

/-- Finite inner averages of a type III factor approximate scalars. -/
theorem publishedDixmierOfTypeIII (hM : TypeIIIFactor M) : PublishedDixmierAveraging M := by
  intro x hx
  obtain ⟨z, hz⟩ := exists_scalar_mem_closed_orbit x (fun ε hε =>
    hM.exists_scalar_average ⟨x, hx.1⟩ ε hε)
  exact ⟨z • (1 : H →L[ℂ] H),
    (concreteCenter M).toStarSubalgebra.smul_mem (concreteCenter M).one_mem _, hz⟩

end

end KadisonKastler

end OAI
