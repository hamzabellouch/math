import OAI.Analysis.KadisonKastler.CornerTracialVector
import OAI.Analysis.KadisonKastler.AdjustedCornerState
import OAI.Analysis.KadisonKastler.ProperInfiniteProjectionCopies
import OAI.Analysis.KadisonKastler.SemifiniteFactor

namespace OAI

/-! # A semifinite diffuse source factor has a nonfactorial modular core -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem regularCore_not_factor_of_typeIIInfinity (hM : TypeIIInfinityFactor M) (Ω : H)
    (hs : Function.Injective (algebraVectorMap M Ω))
    (hc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  let D := (hM.nonempty_finiteMatrixCornerData publishedProperInfiniteProjectionCopies).some
  let E := typeIIIInitialSpace D.projection
  have hE : E.starProjection ∈ M := D.matrix.zero_zero ▸ D.matrix_mem 0 0
  obtain ⟨η, _, hηs, hηt⟩ := exists_corner_tracial_vector hE D.corner_isII1 Ω hs
  have hpE : D.projection.val.val = E.starProjection := typeIIIInitialSpace_projection D.projection
  have hηp : D.projection.val.val η.val = η.val := by
    rw [hpE]
    exact Submodule.starProjection_eq_self_iff.mpr η.property
  have hηfaith : ∀ a : Algebra M, a.val η.val = 0 → a * D.projection.val = 0 := by
    intro a ha
    apply Subtype.ext
    change a.val * D.projection.val.val = 0
    rw [hpE]
    exact hηs a ha
  have hηtrace : ∀ a b : Algebra M,
      inner ℂ η.val ((D.projection.val * a * D.projection.val * b * D.projection.val).val η.val) =
        inner ℂ η.val ((D.projection.val * b * D.projection.val * a * D.projection.val).val η.val) := by
    intro a b
    change inner ℂ η.val ((D.projection.val.val * a.val * D.projection.val.val * b.val *
      D.projection.val.val) η.val) =
      inner ℂ η.val ((D.projection.val.val * b.val * D.projection.val.val * a.val *
      D.projection.val.val) η.val)
    rw [hpE]
    exact hηt a b
  exact regularCore_not_factor_of_corner_trace_vector D.projection D.projection_nonzero
    Ω η.val hs hc hηp hηfaith hηtrace U hU hn hm

end

end KadisonKastler

end OAI
