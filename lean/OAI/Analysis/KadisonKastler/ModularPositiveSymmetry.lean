import OAI.Analysis.KadisonKastler.ModularPositiveOperator
import OAI.Analysis.KadisonKastler.ModularGraphInvariance

namespace OAI

/-! # Inverse and group symmetries of the positive modular operator

All identities concern the full closed graph. The inverse is densely defined,
and polar conjugation exchanges its two coordinates.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularPositiveOperator_ker :
    (modularPositiveOperator J Ω hsep hcyc).ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot']
  intro x hx
  obtain ⟨a, ha, hb⟩ := (modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mp
    (LinearPMap.mem_graph _ x)
  have haz : a = 0 := (tomitaGraphComplementRoot_injective J Ω hsep hcyc)
    (hb.trans (hx.trans (map_zero _).symm))
  apply Subtype.ext
  simp only [← ha, haz, map_zero, Submodule.coe_zero]

include hsep hcyc in
theorem tomitaGraphComplementRoot_dense :
    DenseRange (tomitaGraphComplementRoot (M := M) J Ω) := by
  change Dense ((tomitaGraphComplementRoot (M := M) J Ω).range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, ContinuousLinearMap.orthogonal_range]
  have he : (tomitaGraphComplementRoot (M := M) J Ω).adjoint =
      tomitaGraphComplementRoot (M := M) J Ω :=
    (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint.star_eq
  rw [he]
  exact LinearMap.ker_eq_bot.mpr (tomitaGraphComplementRoot_injective J Ω hsep hcyc)

theorem modularPositiveOperator_range :
    (Set.range (modularPositiveOperator J Ω hsep hcyc)) =
      Set.range (tomitaGraphComplementRoot (M := M) J Ω) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, _, ha⟩ := (modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mp
      (LinearPMap.mem_graph _ x)
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    have hg := (modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mpr ⟨a, rfl, rfl⟩
    obtain ⟨x, _, hx⟩ := (LinearPMap.mem_graph_iff _).mp hg
    exact ⟨x, hx⟩

theorem modularPositiveOperator_denseRange :
    DenseRange (modularPositiveOperator J Ω hsep hcyc) := by
  change Dense (Set.range (modularPositiveOperator J Ω hsep hcyc))
  rw [modularPositiveOperator_range]
  exact tomitaGraphComplementRoot_dense J Ω hsep hcyc

theorem modularPositiveOperator_inverse_graph_iff (x y : H) :
    (x, y) ∈ (modularPositiveOperator J Ω hsep hcyc).inverse.graph ↔
      (y, x) ∈ (modularPositiveOperator J Ω hsep hcyc).graph := by
  rw [LinearPMap.inverse_graph (modularPositiveOperator_ker J Ω hsep hcyc),
    Submodule.map_equiv_eq_comap_symm]
  rfl

/-- The polar conjugation sends the positive graph to its inverse graph. -/
theorem modularPositiveOperator_conjugate_inverse_graph (x y : H) :
    (tomitaPolarConjugation J Ω hsep hcyc x, tomitaPolarConjugation J Ω hsep hcyc y) ∈
      (modularPositiveOperator J Ω hsep hcyc).inverse.graph ↔
    (x, y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph := by
  rw [modularPositiveOperator_inverse_graph_iff,
    modularPositiveOperator_graph_iff, modularPositiveOperator_graph_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    refine ⟨tomitaPolarConjugation J Ω hsep hcyc a, ?_, ?_⟩
    · rw [tomitaGraphRoot_polar_symm, hb, tomitaPolarConjugation_involutive]
    · rw [← tomitaGraphRoot_polar_apply, ha, tomitaPolarConjugation_involutive]
  · rintro ⟨a, ha, hb⟩
    refine ⟨tomitaPolarConjugation J Ω hsep hcyc a, ?_, ?_⟩
    · rw [tomitaGraphRoot_polar_symm, hb]
    · rw [← tomitaGraphRoot_polar_apply, ha]

section Group

variable [TopologicalSpace.SeparableSpace H]

theorem tomitaGraphComplementRoot_group_apply (t : ℝ) (a : H) :
    tomitaGraphComplementRoot (M := M) J Ω
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) a) =
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaGraphComplementRoot (M := M) J Ω a) := by
  have h := tomitaGraphRoot_group_apply J Ω hsep hcyc t
    (tomitaPolarConjugation J Ω hsep hcyc a)
  have h' := congrArg (tomitaPolarConjugation J Ω hsep hcyc) h
  rw [← tomitaPolarConjugation_group_apply, tomitaGraphRoot_polar_apply,
    tomitaPolarConjugation_involutive, tomitaPolarConjugation_group_apply,
    tomitaGraphRoot_polar_apply, tomitaPolarConjugation_involutive] at h'
  exact h'

theorem modularPositiveOperator_group_graph (t : ℝ) {x y : H}
    (hxy : (x, y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph) :
    ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x,
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) y) ∈
      (modularPositiveOperator J Ω hsep hcyc).graph := by
  obtain ⟨a, rfl, rfl⟩ := (modularPositiveOperator_graph_iff J Ω hsep hcyc x y).mp hxy
  apply (modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mpr
  exact ⟨_, tomitaGraphRoot_group_apply J Ω hsep hcyc t a,
    tomitaGraphComplementRoot_group_apply J Ω hsep hcyc t a⟩

theorem modularPositiveOperator_group_domain (t : ℝ) {x : H}
    (hx : x ∈ (modularPositiveOperator J Ω hsep hcyc).domain) :
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) x ∈
      (modularPositiveOperator J Ω hsep hcyc).domain := by
  obtain ⟨y, hxy⟩ := LinearPMap.mem_domain_iff.mp hx
  exact LinearPMap.mem_domain_of_mem_graph
    (modularPositiveOperator_group_graph J Ω hsep hcyc t hxy)

end Group

end

end KadisonKastler

end OAI
