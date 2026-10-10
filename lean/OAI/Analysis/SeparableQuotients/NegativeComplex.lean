import OAI.Analysis.SeparableQuotients.ProductQuotients

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set TopologicalSpace
open scoped Classical
universe u

lemma HasSeparableQuotient.of_equiv {𝕜 : Type} [RCLike 𝕜]
    {X Z : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (d : X ≃L[𝕜] Z)
    (h : HasSeparableQuotient 𝕜 Z) : HasSeparableQuotient 𝕜 X := by
  obtain ⟨Y,hYn,hYs,hYc,hYsep,hYi,T,hT⟩ := h
  let := hYn
  let := hYs
  exact ⟨Y,hYn,hYs,hYc,hYsep,hYi,T.comp d.toContinuousLinearMap,hT.comp d.surjective⟩

/-- A complex quotient gives a real quotient of the underlying real space. -/
lemma HasSeparableQuotient.restrictScalars {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X]
    [IsScalarTower ℝ ℂ X]
    (h : HasSeparableQuotient ℂ X) : HasSeparableQuotient ℝ X := by
  obtain ⟨Y,hYn,hYs,hYc,hYsep,hYi,T,hT⟩ := h
  let := hYn
  let := hYs
  let : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ ℂ Y
  have hi : ¬ FiniteDimensional ℝ Y := by
    intro hh
    let := hh
    exact hYi (Module.Finite.of_restrictScalars_finite ℝ ℂ Y)
  exact ⟨Y,inferInstance,inferInstance,hYc,hYsep,hi,T.restrictScalars ℝ,hT⟩

/-- A real space without a separable quotient has a complexification without a complex separable quotient. -/
lemma complexify_noSQ (X : Type u) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (h : ¬ HasSeparableQuotient ℝ X) :
    ¬ HasSeparableQuotient ℂ (Complexify X) := by
  intro hh
  have hr := hh.restrictScalars
  have hp := hr.of_equiv (Complexify.pairEquiv X).symm
  exact (hasSQ_prod_cases hp).elim h h

/-- CH refutes the complex separable quotient assertion in every universe. -/
theorem negative_complex (hCH : CH) : ¬ SQ.{u} ℂ := by
  intro hSQ
  apply negative_real.{u} hCH
  intro X _ _ _ hXi
  by_contra hX
  have hc := hSQ (Complexify X) (Complexify.infinite X hXi)
  exact complexify_noSQ X hX hc

end SeparableQuotient

end

end OAI
