import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamily

namespace OAI

/-! Finite substitution for the actual charted mean family. The threshold
here is for the fixed geometric and scale data in the supplied charts. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)

theorem charted_family_majorants (hρ : 0 < ρ) (hτ : 0 < τ) (hs : 0 < (s : ℝ))
    (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q : ℕ) :
    ∃ β κ : ℕ → ℝ → ℝ, ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r
        (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (chartedFamilyMean d hρ δ q)) β κ := by
  classical
  choose β κ hm using fun i => (d i).majorants hρ hτ hs hτs hs1 hε hε1 hsmall q
  refine ⟨(fun m C => 1 + ∑ i, β i m C), (fun m C => 1 + ∑ i, κ i m C), ?_⟩
  intro δ hδ
  exact MeanBounds.finset_rescaled isOpen_univ.uniqueDiffOn s.coe_nonneg Finset.univ
    (fun i => (d i).mean hρ δ q) (fun _ => tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))
    (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) β κ (fun _ _ => le_rfl)
    (fun i _ => hm i δ hδ)

theorem finite_charted_mean_adjustment (hρ : 0 < ρ) (hτ : 0 < τ) (hs : 0 < (s : ℝ))
    (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q steps : ℕ)
    {H : SmallModes.Base → Tensor} {r₀ : ℝ} (hgap : r₀ < r)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ x, ‖H x - reference x‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound Set.univ s m (C m) H) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → τ / s + ε / τ ^ tensorLoss P ≤ η₀ →
      ∀ j ≤ steps,
        ContDiff ℝ ∞ (fixedTrial H (chartedFamilyMean d hρ δ q) j) ∧
        InTrialBall Set.univ reference r (fixedTrial H (chartedFamilyMean d hρ δ q) j) ∧
        (∀ m, WeightedBound Set.univ s m (sizeBound L C β j m)
          (fixedTrial H (chartedFamilyMean d hρ δ q) j)) ∧
        (∀ m, WeightedBound Set.univ s m
          (differenceBound L C β κ j m * (τ / s + ε / τ ^ tensorLoss P) ^ (j + 1))
          (fixedTrial H (chartedFamilyMean d hρ δ q) j +
            chartedFamilyMean d hρ δ q (fixedTrial H (chartedFamilyMean d hρ δ q) j) - H)) := by
  obtain ⟨β,κ,hm⟩ := charted_family_majorants d hρ hτ hs hτs hs1 hε hε1 hsmall q
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := finite_substitution_uniform (B := β) (K := κ)
    isOpen_univ.uniqueDiffOn s.coe_nonneg hgap hC hH.contDiffOn (fun x _ => hH0 x) hbH steps
  refine ⟨β,κ,η₀,hη₀,hη₁,?_⟩
  intro δ hδ hsmall' j hj
  have hη : 0 < τ / s + ε / τ ^ tensorLoss P :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  obtain ⟨ha,hb,hc,hd⟩ := ht _ (hm δ hδ) _ hη hsmall' j hj
  exact ⟨contDiffOn_univ.mp (by simpa only [trial_rescaledMean hη.ne'] using ha),
    by simpa only [trial_rescaledMean hη.ne'] using hb,
    by simpa only [trial_rescaledMean hη.ne'] using hc,
    by simpa only [trial_rescaledMean hη.ne', rescaledMean_self hη.ne'] using hd⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
