import OAI.Analysis.KadisonKastler.CornerHomogeneityApplication

namespace OAI

/-! # State homogeneity with a fixed centralizing projection

The two normalized corner comparisons combine to a unitary commuting
with the original projection, under the vector-state specialization of
Connes--Størmer homogeneity.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem sandwichFunctional_real_smul (φ : Algebra M →L[ℂ] ℂ) (u : Algebra M) (r : ℝ) :
    sandwichFunctional (r • φ) u=r • sandwichFunctional φ u := by
  ext a
  rfl

theorem vectorCornerState_sandwich (p : AlgebraProjection M) (ξ : H)
    (u : Algebra M) (hu : star u*u=p.val) (hu' : u*star u=p.val) :
    sandwichFunctional (vectorCornerState p ξ) u =
      (projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) u := by
  change sandwichFunctional ((projectionVectorWeight p ξ)⁻¹ •
    vectorFunctional (p.val.val ξ)) u = _
  rw [← cornerFunctional_vectorFunctional p ξ,
    ← sandwichFunctional_projection _ _ p.property,sandwichFunctional_real_smul,
    sandwichFunctional_comp,(cornerUnitary_supports p u hu hu').2]

theorem TypeIIIFactor.central_projection_state_comparison
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M)
    (hhom : FaithfulVectorStateHomogeneity M) (p : AlgebraProjection M)
    (hp0 : p.val≠0) (hp1 : p.val≠1) (ξ ζ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hnξ : ‖ξ‖=1)
    (hζ : Function.Injective (algebraVectorMap M ζ)) (hnζ : ‖ζ‖=1)
    (hcξ : ∀ x : Algebra M, vectorFunctional ξ (p.val*x)=vectorFunctional ξ (x*p.val))
    (hcζ : ∀ x : Algebra M, vectorFunctional ζ (p.val*x)=vectorFunctional ζ (x*p.val))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : unitary (Algebra M), w.val*p.val=p.val*w.val ∧
      ‖sandwichFunctional (vectorFunctional ξ) w.val-vectorFunctional ζ‖ ≤
        ε+2*|projectionVectorWeight p ξ-projectionVectorWeight p ζ| := by
  let q : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  have hq : q.val≠0 := sub_ne_zero.mpr hp1.symm
  obtain ⟨u,hu,hu',huclose⟩ := hM.corner_comparison_of_vector_state_homogeneity
    hhom p hp0 ξ ζ hξ hζ ε hε
  obtain ⟨v,hv,hv',hvclose⟩ := hM.corner_comparison_of_vector_state_homogeneity
    hhom q hq ξ ζ hξ hζ ε hε
  let w := complementaryCornerUnitary p u v hu hu' hv hv'
  have hc := complementaryCornerUnitary_compressions p u v hu hu' hv hv'
  refine ⟨w,hc.2.1.trans hc.1.symm,?_⟩
  rw [sandwichFunctional_vectorFunctional]
  apply patched_vector_state_norm_le p u v hu hu' hv hv' ξ ζ
    hξ hnξ hζ hnζ hp0 hp1 hcξ hcζ ε
  · rw [← vectorCornerState_sandwich p ξ u hu hu']
    exact huclose.le
  · have he : 1-projectionVectorWeight p ξ=projectionVectorWeight q ξ := by
      have hh := projectionVectorWeight_add_complement p ξ
      rw [hnξ] at hh
      change projectionVectorWeight p ξ+projectionVectorWeight q ξ=1^2 at hh
      linarith
    rw [he,← vectorCornerState_sandwich q ξ v hv hv']
    exact hvclose.le

end

end KadisonKastler

end OAI
