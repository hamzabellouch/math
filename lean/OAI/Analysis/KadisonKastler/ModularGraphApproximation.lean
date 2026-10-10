import OAI.Analysis.KadisonKastler.ModularGraphInvariance

namespace OAI

/-! # Algebraic approximation of modular translates in graph norm

The full closed-graph invariance gives simultaneous approximation of a
translated algebra vector and its adjoint vector by the same algebra
element. These are graph-norm approximations; no operator-norm bound is
asserted.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))

include hsep

/-- Simultaneous approximation of both coordinates of the closed graph. -/
theorem tomitaClosed_graph_approximate {x y : H}
    (hxy : (x, y) ∈ (tomitaClosedLinearOperator M J Ω 1).graph)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : Algebra M, ‖a.val Ω - x‖ < ε ∧ ‖J (star a.val Ω) - y‖ < ε := by
  rw [tomitaClosedLinearOperator_graph J Ω 1 hsep] at hxy
  let v := tomitaProductCoordinates.symm (x, y)
  have hv : v ∈ closure (Set.range (rescaledGraphMap M J Ω 1)) := hxy
  obtain ⟨w, ⟨a, rfl⟩, ha⟩ := (Metric.mem_closure_iff.mp hv) ε hε
  refine ⟨a, ?_, ?_⟩
  · have h := (PiLp.dist_apply_le (rescaledGraphMap M J Ω 1 a) v 0).trans_lt
      (show dist (rescaledGraphMap M J Ω 1 a) v < ε by rwa [dist_comm])
    have hv0 : v 0 = x := rfl
    simpa only [rescaledGraphMap_apply, rescaledGraphVector_zero, hv0, dist_eq_norm] using h
  · have h := (PiLp.dist_apply_le (rescaledGraphMap M J Ω 1 a) v 1).trans_lt
      (show dist (rescaledGraphMap M J Ω 1 a) v < ε by rwa [dist_comm])
    have hv1 : v 1 = y := rfl
    simpa only [rescaledGraphMap_apply, rescaledGraphVector_one, hv1, one_smul, dist_eq_norm] using h

variable [TopologicalSpace.SeparableSpace H]
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modular_translate_graph_approximate (t : ℝ) (a : Algebra M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Algebra M,
      ‖b.val Ω - (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (a.val Ω)‖ < ε ∧
      ‖star b.val Ω - (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (star a.val Ω)‖ < ε := by
  have hg := modularStrongGroup_preserves_tomita_graph J Ω hsep hcyc t
    (tomitaClosedLinearOperator_algebraic_graph J Ω 1 hsep a)
  simp only [one_smul, J.symm_apply_apply] at hg
  obtain ⟨b, hb, hb'⟩ := tomitaClosed_graph_approximate J Ω hsep hg hε
  refine ⟨b, hb, ?_⟩
  rwa [← J.map_sub, J.norm_map] at hb'

end

end KadisonKastler

end OAI
