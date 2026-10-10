import OAI.Analysis.KadisonKastler.NestAveraging

namespace OAI

/-! # The published nest distance input and its invariant approximant

William Arveson, *Interpolation problems in nest algebras*, J. Functional
Analysis 20 (1975), 208–233, Theorem 1.1, p.212, with the finite-chain
reduction in its proof and Lemma 1, p.209. We retain only its upper distance
bound for a real-indexed increasing family of orthogonal projections.
Adjoining strong limits, zero and identity does not change the algebra
or the upper bound. No analytic multiplier or perturbation conclusion
is included in the published input.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- The approximation consequence of Arveson's nest distance formula,
with explicit slack instead of a nearest-point assertion. -/
def PublishedRealNestDistance : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (P : ℝ → H →L[ℂ] H), (∀ a, IsStarProjection (P a)) →
      (∀ a b, a ≤ b → P a * P b = P a) →
      ∀ (T : H →L[ℂ] H) (δ η : ℝ), 0 ≤ δ → 0 < η →
      (∀ a, ‖(1 - P a) * T * P a‖ ≤ δ) →
      ∃ S : H →L[ℂ] H, PreservesProjectionNest P S ∧ ‖S - T‖ < δ + η

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- A small nest defect of an invariant operator produces an invariant
nest-preserving approximant, by applying the published distance bound
before the already constructed coefficient average. -/
theorem exists_invariant_nest_approximant
    (hpub : PublishedRealNestDistance.{u}) (m : ScalarInvariantMean G)
    (P : ℝ → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hmono : ∀ a b, a ≤ b → P a * P b = P a)
    (U : G →* unitary (H →L[ℂ] H))
    (hperm : ∀ g a, ∃ b, P a = unitaryConj (U g) (P b))
    (T : H →L[ℂ] H) (hfixed : ∀ g, unitaryConj (U g) T = T)
    {δ : ℝ} (hδ : 0 < δ) (hdefect : ∀ a, ‖(1 - P a) * T * P a‖ ≤ δ) :
    ∃ S : H →L[ℂ] H, PreservesProjectionNest P S ∧
      (∀ g, unitaryConj (U g) S = S) ∧ ‖S - T‖ < 2 * δ := by
  obtain ⟨S, hS, hST⟩ := hpub H P hP hmono T δ δ hδ.le hδ hdefect
  refine ⟨m.averageConjugation U S,
    m.averageConjugation_preservesProjectionNest P U S hS hperm,
    m.averageConjugation_invariant U S, ?_⟩
  exact (m.norm_averageConjugation_sub_fixed_le U S T hfixed).trans_lt (by linarith)

end

end KadisonKastler

end OAI
