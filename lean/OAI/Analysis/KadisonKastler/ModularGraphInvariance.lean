import OAI.Analysis.KadisonKastler.TomitaRootDomain
import OAI.Analysis.KadisonKastler.ModularRootCommutation

namespace OAI

/-! # Invariance of the full closed Tomita graph

Commutation with the graph square root and polar conjugation gives domain
invariance for the constructed group on the full closed operator domain.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaPolarConjugation_group_apply (t : ℝ) (a : H) :
    tomitaPolarConjugation J Ω hsep hcyc
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) a) =
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaPolarConjugation J Ω hsep hcyc a) := by
  have h := congrArg (fun T : H →L[ℂ] H => T (tomitaPolarConjugation J Ω hsep hcyc a))
    (modularStrongGroup_polar_conjugation J Ω hsep hcyc t)
  change tomitaPolarConjugation J Ω hsep hcyc
    ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaPolarConjugation J Ω hsep hcyc (tomitaPolarConjugation J Ω hsep hcyc a))) = _ at h
  rw [tomitaPolarConjugation_involutive] at h
  exact h

theorem tomitaGraphRoot_group_apply (t : ℝ) (a : H) :
    tomitaGraphRoot (M := M) J Ω
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) a) =
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaGraphRoot (M := M) J Ω a) :=
  (congrArg (fun T : H →L[ℂ] H => T a)
    (modularStrongGroup_commute_root J Ω hsep hcyc t).eq).symm

theorem modularStrongGroup_preserves_tomita_graph (t : ℝ) {x y : H}
    (hxy : (x, y) ∈ (tomitaClosedLinearOperator M J Ω 1).graph) :
    ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x,
      J ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) (J.symm y))) ∈
      (tomitaClosedLinearOperator M J Ω 1).graph := by
  obtain ⟨a, ha, hb⟩ := (tomitaClosedLinearOperator_graph_iff J Ω hsep hcyc x y).mp hxy
  apply (tomitaClosedLinearOperator_graph_iff J Ω hsep hcyc _ _).mpr
  refine ⟨(modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) a, ?_, ?_⟩
  · rw [tomitaGraphRoot_group_apply, ha]
  · rw [tomitaPolarConjugation_group_apply, tomitaGraphRoot_group_apply,
      ← hb, J.symm_apply_apply]

theorem modularStrongGroup_preserves_tomita_domain (t : ℝ) {x : H}
    (hx : x ∈ (tomitaClosedLinearOperator M J Ω 1).domain) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x ∈
      (tomitaClosedLinearOperator M J Ω 1).domain := by
  obtain ⟨y, hxy⟩ := LinearPMap.mem_domain_iff.mp hx
  exact LinearPMap.mem_domain_of_mem_graph
    (modularStrongGroup_preserves_tomita_graph J Ω hsep hcyc t hxy)

theorem tomitaClosedLinearOperator_group_apply (t : ℝ) (x : (tomitaClosedLinearOperator M J Ω 1).domain) :
    tomitaClosedLinearOperator M J Ω 1
      ⟨(modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x.val,
        modularStrongGroup_preserves_tomita_domain J Ω hsep hcyc t x.property⟩ =
      J ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (J.symm (tomitaClosedLinearOperator M J Ω 1 x))) := by
  exact (tomitaClosedLinearOperator M J Ω 1).mem_graph_snd_inj
    (LinearPMap.mem_graph _ _)
    (modularStrongGroup_preserves_tomita_graph J Ω hsep hcyc t (LinearPMap.mem_graph _ x)) rfl

end

end KadisonKastler

end OAI
