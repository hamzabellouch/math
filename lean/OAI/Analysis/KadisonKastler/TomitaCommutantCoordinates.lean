import OAI.Analysis.KadisonKastler.TomitaAdjointCoordinates
import OAI.Analysis.KadisonKastler.TomitaAdjointCore
import OAI.Analysis.KadisonKastler.ModularGraphApproximation

namespace OAI

/-! # Commutant vectors in the positive Tomita coordinates

The adjoint identity on the commutant orbit and the full adjoint graph
parametrization put its polar-conjugated vectors in the original closed
Tomita graph, with simultaneous algebraic approximation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaCommutant_root_coordinates (b : Algebra M.commutant) :
    ∃ a : H,
      tomitaGraphRoot (M := M) J Ω a = tomitaPolarConjugation J Ω hsep hcyc (b.val Ω) ∧
      tomitaGraphComplementRoot (M := M) J Ω a = star b.val Ω := by
  have hg := LinearPMap.mem_graph (tomitaClosedLinearOperator M J Ω 1).adjoint
    ⟨J (b.val Ω), tomitaAdjoint_commutant_mem J Ω hsep b⟩
  rw [tomitaAdjoint_commutant_apply J Ω hsep hcyc b] at hg
  obtain ⟨a, ha, hb⟩ := (tomitaAdjoint_graph_iff J Ω hsep hcyc _ _).mp hg
  refine ⟨a, ?_, hb⟩
  have h := J.injective ha
  have h' := congrArg (tomitaPolarConjugation J Ω hsep hcyc) h
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at h'
  exact h'

theorem tomitaCommutant_conjugate_graph (b : Algebra M.commutant) :
    (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω),
      J (tomitaPolarConjugation J Ω hsep hcyc (star b.val Ω))) ∈
        (tomitaClosedLinearOperator M J Ω 1).graph := by
  obtain ⟨a, ha, hb⟩ := tomitaCommutant_root_coordinates J Ω hsep hcyc b
  apply (tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc _ _).mpr
  refine ⟨a, ha, ?_⟩
  change J (tomitaPolarConjugation J Ω hsep hcyc (tomitaGraphComplementRoot (M := M) J Ω a)) = _
  rw [hb]

theorem tomitaCommutant_conjugate_approximate (b : Algebra M.commutant)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : Algebra M,
      ‖a.val Ω - tomitaPolarConjugation J Ω hsep hcyc (b.val Ω)‖ < ε ∧
      ‖star a.val Ω - tomitaPolarConjugation J Ω hsep hcyc (star b.val Ω)‖ < ε := by
  obtain ⟨a, ha, hb⟩ := tomitaClosed_graph_approximate J Ω hsep
    (tomitaCommutant_conjugate_graph J Ω hsep hcyc b) hε
  refine ⟨a, ha, ?_⟩
  rwa [← J.map_sub, J.norm_map] at hb

end

end KadisonKastler

end OAI
