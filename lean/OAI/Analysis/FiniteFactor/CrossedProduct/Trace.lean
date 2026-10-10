import OAI.Analysis.FiniteFactor.CrossedProduct.ConjugationVacuum

namespace OAI

namespace FiniteFactor
noncomputable section

/-- Traciality of the actual, previously constructed normal vacuum functional. -/
theorem sourceVacuumFunctional_tracial (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    sourceVacuumFunctional (A * B) = sourceVacuumFunctional (B * A) := by
  have hh := sourceConjugation_inner_symm θ (A sourceVacuum) (B sourceVacuum)
  rw [sourceConjugation_algebra_vacuum θ hA, sourceConjugation_algebra_vacuum θ hB] at hh
  have hc := congrArg (starRingEnd ℂ) hh
  rw [inner_conj_symm, inner_conj_symm] at hc
  change inner ℂ sourceVacuum (A (B sourceVacuum)) = inner ℂ sourceVacuum (B (A sourceVacuum))
  rw [← ContinuousLinearMap.adjoint_inner_left A (B sourceVacuum) sourceVacuum,
    ← ContinuousLinearMap.adjoint_inner_left B (A sourceVacuum) sourceVacuum]
  exact hc.symm

/-- Equality of the two square expectations is derived from traciality. -/
theorem sourceVacuumFunctional_square_commute (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceVacuumFunctional (star H * H) = sourceVacuumFunctional (H * star H) :=
  sourceVacuumFunctional_tracial θ (star_mem hH) hH

end
end FiniteFactor

end OAI
