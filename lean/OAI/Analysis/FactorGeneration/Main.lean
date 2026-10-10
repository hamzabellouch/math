import OAI.Analysis.FactorGeneration.Generation
import OAI.Analysis.FactorGeneration.PredualContinuity
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

namespace Generator

/-! Single generation of a finite diffuse factor with a separable Banach predual,
using its faithful normal trace and given-predual continuity. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem single_generation_of_II1_separable_predual
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S)
    (hsep : HasSeparablePredual S) : SinglyGenerated S := by
  let M := vonNeumannOfWOTClosed S hS.weaklyClosed
  have hf : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    obtain ⟨z, hz⟩ := hS.factor c hc
    exact ⟨z, hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  have hunit : (1 : M.toStarSubalgebra) ≠ 0 := by
    intro h
    exact hS.nonzero (congrArg Subtype.val h).symm
  let E := Tracial.TraceFreePreHilbert hf hS.diffuse hS.finite hunit
  let : NormedAddCommGroup E :=
    Tracial.traceFreePreHilbertNormedAddCommGroup hf hS.diffuse hS.finite hunit
  let : InnerProductSpace ℂ E :=
    Tracial.traceFreePreHilbertInnerProductSpace hf hS.diffuse hS.finite hunit
  let N := Tracial.traceFreeHilbertClosure hf hS.diffuse hS.finite hunit
  let τ := Tracial.traceFreeHilbertClosureTrace hf hS.diffuse hS.finite hunit
  have hN := Tracial.traceFreeHilbertClosure_isII1Factor hf hS.diffuse hS.finite hunit
  have hpre := Tracial.traceFreeHilbertClosure_hasSeparablePredual hf hS.diffuse hS.finite hunit hsep
  have htrace := Tracial.traceOrbit_isSeparable_of_separablePredual τ hpre
  exact Tracial.traceFreeHilbert_singlyGenerated_pullback hf hS.diffuse hS.finite hunit
    (Tracial.singlyGenerated_of_tracialRepresentation hN τ htrace)

theorem mainTarget : @MainTarget H _ _ _ :=
  single_generation_of_II1_separable_predual

end

end Generator

end OAI
