import OAI.Analysis.KadisonKastler.ModularPositiveOperator
import OAI.Analysis.KadisonKastler.ModularGraphApproximation
import OAI.Analysis.KadisonKastler.ModularRightAction

namespace OAI

/-! # Algebraic approximation in the positive modular graph -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem positiveGraph_algebraic_approximate
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    {x y : H} (hxy : (x,y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : Algebra M, ‖a.val Ω-x‖ < ε ∧ ‖d.rightAction a Ω-y‖ < ε := by
  obtain ⟨z,hz,hz'⟩ := (modularPositiveOperator_graph_iff J Ω hsep hcyc x y).mp hxy
  have hg : (x,tomitaLinearPolarUnitary J Ω hsep hcyc y) ∈
      (tomitaClosedLinearOperator M J Ω 1).graph := by
    apply (tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc _ _).mpr
    exact ⟨z,hz,congrArg (tomitaLinearPolarUnitary J Ω hsep hcyc) hz'⟩
  obtain ⟨a,ha,hb⟩ := tomitaClosed_graph_approximate J Ω hsep hg hε
  refine ⟨a,ha,?_⟩
  have he : ‖d.rightAction a Ω-y‖ =
      ‖J (star a.val Ω)-tomitaLinearPolarUnitary J Ω hsep hcyc y‖ := by
    change ‖d.conjugation (star a.val (d.conjugation Ω))-y‖=_
    rw [d.fixes_vector,hd,tomitaLinearPolarUnitary_apply,← J.map_sub,J.norm_map]
    calc
      _ = ‖tomitaPolarConjugation J Ω hsep hcyc
          (star a.val Ω-tomitaPolarConjugation J Ω hsep hcyc y)‖ := by
        rw [map_sub,tomitaPolarConjugation_involutive]
      _ = _ := (tomitaPolarConjugation J Ω hsep hcyc).norm_map _
  rwa [he]

end

end KadisonKastler

end OAI
