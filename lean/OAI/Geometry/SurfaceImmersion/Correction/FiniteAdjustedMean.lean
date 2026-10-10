import OAI.Geometry.SurfaceImmersion.Correction.AssembledZeroMean

namespace OAI

/-! The actual quadratic zero-phase tensor is adjusted to its target by a
finite construction; no derivative-losing infinite iteration is used. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.PhaseMean
open SmallModes WeightedEstimates FiniteMean
variable {ι : Type*} {s r ρ R₀ : ℝ} {reference : Base → Tensor} {n L : ℕ}

theorem finite_adjusted_quadratic_mean (a : Finset ι)
    (c : ι → CombinedMeanChart s r ρ R₀ reference n L)
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (q steps : ℕ)
    {H : Base → Tensor} {r₀ : ℝ} (hgap : r₀ < r)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ x, ‖H x - reference x‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound Set.univ s m (C m) H)
    (hdecomp : ∀ A : Base → Tensor, ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      ∀ x, ∑ i ∈ a, (c i).leading A x = A x) :
    let ℓ := a.sup (fun i => (c i).loss q)
    let p₀ := a.sup (fun i => (c i).exponent)
    ∃ B K : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ (δ τ ε : ℝ) (p : ℕ), 0 < δ → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      p₀ ≤ p → τ / s + ε / τ ^ p ≤ η₀ →
      ∀ R : ∀ i, (c i).Operator,
      (∀ i ∈ a, (c i).OperatorBound hs τ ε p (R i)) →
      ∀ j ≤ steps, ∃ A : Base → Tensor, ContDiff ℝ ∞ A ∧
        InTrialBall Set.univ reference r A ∧
        (∀ m, WeightedBound Set.univ s m (sizeBound ℓ C B j m) A) ∧
        (∀ m, WeightedBound Set.univ s m (δ ^ 2 *
          (differenceBound ℓ C B K j m * (τ / s + ε / τ ^ p) ^ (j + 1)))
          (assembledQuadraticMean a c hρ δ τ ε R q A - δ ^ 2 • H)) := by
  obtain ⟨B, K, η₀, hη₀, hη₁, ht⟩ := finite_assembled_combined_mean a c hs hs1 hρ q steps hgap hC hH hH0 hbH
  refine ⟨B, K, η₀, hη₀, hη₁, ?_⟩
  intro δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR j hj
  obtain ⟨ha, hb, hc, hd⟩ := ht δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR j hj
  let A := fixedTrial H (assembledCombinedMean a c hρ δ τ ε R q) j
  refine ⟨A, ha, hb, hc, ?_⟩
  intro m
  exact assembledQuadraticMean_residual a c hρ δ τ ε hδ.ne' hτ.ne' R q ha hH hb (hdecomp A ha hb) (hd m)

end ClosedSurfaceR4.PhaseMean

end

end OAI
