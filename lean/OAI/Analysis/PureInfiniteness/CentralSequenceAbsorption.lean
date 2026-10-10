import OAI.Analysis.Nuclearity.TensorMultiplierAction
import OAI.Analysis.PureInfiniteness.Main
import OAI.Analysis.JiangSu.Absorption.AbsorptionCriterion
import OAI.Analysis.JiangSu.TensorProducts.TensorIdeal

namespace OAI

/-!
# Absorption from the published central-sequence embedding

The embedding below is into `(Aω ∩ A') / Ann(A, Aω)`.  This is the
central-sequence embedding immediately preceding Proposition 4.4 in Kirchberg,
*Central sequences in C*-algebras and strongly purely infinite algebras*,
Abel Symposia 1 (2006), 175--231. The structural hypotheses specialize
Proposition 4.4(1),(3),(5) and Remark 4.6 to the absorbing algebra: nuclearity,
simplicity, and a connected approximate half-flip in a faithful C*-completion
of its algebraic tensor square.  Tensor absorption follows from quotient intertwining.
-/

noncomputable section
open scoped MultiplierAlgebra TensorProduct
open Filter

namespace WeakPureInfiniteness

universe u v
variable {A : Type v} {D : Type u}
  [NonUnitalCStarAlgebra A] [CStarAlgebra D]

lemma tensorMultiplier_polynomial_mem (c : A × D →₀ ℂ) :
    DoubleCentralizer.coeHom (minimalPolynomial c) ∈
      NonunitalTensor.coefficientSpan
        (DoubleCentralizer.coeHom.comp (minimalLeftEmbedding A D))
        (tensorRightFactorHom (A := A) (D := D)) := by
  classical
  let S := NonunitalTensor.coefficientSpan
    (DoubleCentralizer.coeHom.comp (minimalLeftEmbedding A D))
    (tensorRightFactorHom (A := A) (D := D))
  change DoubleCentralizer.coeHom (minimalPolynomial c) ∈ S
  simp only [minimalPolynomial, Finsupp.sum, map_sum, map_smul]
  apply S.sum_mem
  intro z hz
  apply S.smul_mem
  rw [← tensorMultiplier_coefficient]
  exact NonunitalTensor.coefficientSpan_mem _ _ z.1 z.2

lemma tensorMultiplier_coefficient_dense (b : MinimalTensor A D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ l : List (A × D),
      ‖NonunitalRelative.coefficientSum
        (DoubleCentralizer.coeHom.comp (minimalLeftEmbedding A D))
        (tensorRightFactorHom (A := A) (D := D)) l -
          DoubleCentralizer.coeHom b‖ < ε := by
  obtain ⟨c, hc⟩ := minimalPolynomial_denseRange.exists_dist_lt b hε
  obtain ⟨l, hl⟩ := (NonunitalTensor.mem_span_iff _ _ _).mp
    (tensorMultiplier_polynomial_mem c)
  refine ⟨l, ?_⟩
  rw [hl, ← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le
    (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := MinimalTensor A D)) _).trans_lt
    (by simpa only [dist_eq_norm, norm_sub_rev] using hc)

variable [Nontrivial A] [Nontrivial D]
  [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A]
  [TopologicalSpace.SeparableSpace D]
  {T : Type*} [CStarAlgebra T]

/-- The nonunital tensor absorption argument from an actual central embedding. -/
theorem minimalTensor_equiv_of_central_embedding
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (φ : D →⋆ₐ[ℂ] NonunitalGamma.CentralSequenceAlgebra (A := A) U)
    (hD : Pureness.IsNuclear.{u,u} D) (hs : Pureness.TopologicallySimple D)
    (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) (hf : Function.Injective f) (hd : DenseRange f)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip f) :
    Nonempty (A ≃⋆ₐ[ℂ] MinimalTensor A D) := by
  let ι := minimalLeftEmbedding A D
  let k := DoubleCentralizer.coeHom (𝕜 := ℂ) (A := MinimalTensor A D)
  have hi : Isometry ι := minimalLeftEmbedding_isometry A D
  have hk : Isometry k := NonUnitalStarAlgHom.isometry k
    (multiplierInclusion_injective _)
  have hj : ∃ a : A, k (ι a) ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    refine ⟨a, ?_⟩
    intro h
    apply ha
    apply hi.injective
    apply hk.injective
    simpa only [map_zero] using h
  exact NonunitalRelative.equiv_of_central_embedding U ι k
    tensorRightFactorHom tensorMultiplier_commute hj φ hD hs f hf hd hh
    (fun b ε hε => tensorMultiplier_coefficient_dense b hε) hi hk
    (fun e b => k.mem_range.mp ((multiplierInclusion_rightIdeal _).mul_left b e))
    (fun b e => k.mem_range.mp (multiplierInclusion_rightIdeal _ b e))

end WeakPureInfiniteness

namespace WeakPureInfiniteness.Campaign

universe u w
variable {A : Type u} [NonUnitalCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A]

local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- Corollary 1.3 from the separate published central-embedding and
connected-half-flip inputs, including the zero algebra.  No absorption
proposition is a premise. -/
theorem nuclear_absorption_from_published_inputs
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (hcentral : Nontrivial A → Nuclear A → StronglyPurelyInfinite A →
      Nonempty (OInfinity →⋆ₐ[ℂ]
        NonunitalGamma.CentralSequenceAlgebra (A := A) U))
    (hD : Pureness.IsNuclear.{1,1} OInfinity)
    (hs : Pureness.TopologicallySimple OInfinity)
    {T : Type w} [CStarAlgebra T]
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T)
    (hf : Function.Injective f) (hd : DenseRange f)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip f)
    (hNuclear : Nuclear A) {n : ℕ} (hn : 1 ≤ n)
    (hF : FixedAmplification A n) : AbsorbsOInfinity A := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let := hA
    exact absorbsOInfinity_of_subsingleton A
  | inr hA =>
    let := hA
    have hS := (nuclear_fixedAmplification hNuclear hn hF).2.2
    obtain ⟨φ⟩ := hcentral hA hNuclear hS
    exact minimalTensor_equiv_of_central_embedding U φ hD hs f hf hd hh

end WeakPureInfiniteness.Campaign

end

end OAI
