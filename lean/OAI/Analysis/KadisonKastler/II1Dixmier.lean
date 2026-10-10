import OAI.Analysis.KadisonKastler.TracialDixmierConclusion
import OAI.Analysis.KadisonKastler.FiniteAverageRepresentation
import OAI.Analysis.KadisonKastler.ScalarOrbitClosure
import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # Diffuse finite-factor Dixmier averaging in every representation -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

omit [Nontrivial H] in
/-- Move to the constructed tracial representation, average there, and pull
the finite list of unitaries back through the isometric algebra equivalence. -/
theorem exists_II1_scalar_average (hM : IsII1Factor M.toStarSubalgebra)
    (x : Algebra M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply x.val - z • (1 : H →L[ℂ] H)‖ < ε := by
  let hf := traceHilbert_factor hM
  let hu := traceHilbert_nonzero hM
  let N := traceFreeHilbertClosure hf hM.diffuse hM.finite hu
  let τ : TracialRepresentation N := traceFreeHilbertClosureTrace hf hM.diffuse hM.finite hu
  let e : Algebra M ≃⋆ₐ[ℂ] Algebra N := traceFreeHilbertEquiv hf hM.diffuse hM.finite hu
  let _ : Nontrivial (TraceFreeHilbert hf hM.diffuse hM.finite hu) := by
    apply nontrivial_of_ne τ.vector 0
    intro h
    have hn := τ.norm_vector
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hN := traceFreeHilbertClosure_isII1Factor hf hM.diffuse hM.finite hu
  obtain ⟨A, z, hA⟩ := exists_tracial_scalar_average τ (traceHilbert_factor hN) hN.diffuse
    (e x) ε hε
  refine ⟨A.pullback e, z, ?_⟩
  rw [A.pullback_norm_error e (traceFreeHilbertEquiv_norm hf hM.diffuse hM.finite hu)]
  exact hA

/-- Dixmier averaging holds in every concrete representation of a type II₁ factor,
without requiring a tracial vector in that representation. -/
theorem publishedDixmierOfII1 (hM : IsII1Factor M.toStarSubalgebra) :
    PublishedDixmierAveraging M := by
  intro x hx
  obtain ⟨z, hz⟩ := exists_scalar_mem_closed_orbit x (fun ε hε =>
    exists_II1_scalar_average hM ⟨x, hx.1⟩ ε hε)
  exact ⟨z • (1 : H →L[ℂ] H),
    (concreteCenter M).toStarSubalgebra.smul_mem (concreteCenter M).one_mem _, hz⟩

end

end KadisonKastler

end OAI
