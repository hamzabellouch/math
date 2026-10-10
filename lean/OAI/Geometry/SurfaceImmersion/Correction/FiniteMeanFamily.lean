import OAI.Geometry.SurfaceImmersion.Correction.FiniteMeanSums

namespace OAI

/-! Finite substitution for a sum of local mean operators. The common loss
and all majorants are fixed before the small parameter and actual operators. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_mean_family {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference H : E → F} {r0 r1 : ℝ} (hgap : r0 < r1)
    (a : Finset ι) (L : ι → ℕ) (L' : ℕ) (hL : ∀ i ∈ a, L i ≤ L')
    (B K : ι → ℕ → ℝ → ℝ) {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m)
    (hH : ContDiffOn ℝ ∞ H U) (hH0 : ∀ x ∈ U, ‖H x - reference x‖ ≤ r0)
    (hbH : ∀ m, WeightedBound U s m (C m) H) (n : ℕ) :
    let B' := fun m C => 1 + ∑ i ∈ a, B i m C
    let K' := fun m C => 1 + ∑ i ∈ a, K i m C
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 ∧ ∀ η, 0 < η → η ≤ η0 →
      ∀ A : ι → (E → F) → E → F,
      (∀ i ∈ a, MeanBounds U s reference r1 (L i) (rescaledMean η (A i)) (B i) (K i)) →
      let T := fun f x => ∑ i ∈ a, A i f x
      ∀ j ≤ n, ContDiffOn ℝ ∞ (fixedTrial H T j) U ∧
        InTrialBall U reference r1 (fixedTrial H T j) ∧
        (∀ m, WeightedBound U s m (sizeBound L' C B' j m) (fixedTrial H T j)) ∧
        (∀ m, WeightedBound U s m (differenceBound L' C B' K' j m * η ^ (j + 1))
          (fixedTrial H T j + T (fixedTrial H T j) - H)) := by
  obtain ⟨η0, h0, h1, hh⟩ := finite_substitution_uniform
    (B := fun m C => 1 + ∑ i ∈ a, B i m C)
    (K := fun m C => 1 + ∑ i ∈ a, K i m C) hU hs hgap hC hH hH0 hbH n
  refine ⟨η0, h0, h1, ?_⟩
  intro η hη hsmall A hA
  have hm := MeanBounds.finset_rescaled hU hs a A L L' B K hL hA
  dsimp only
  intro j hj
  simpa only [trial_rescaledMean hη.ne', rescaledMean_self hη.ne'] using
    hh _ hm η hη hsmall j hj

end ClosedSurfaceR4.FiniteMean

end

end OAI
