import OAI.Geometry.SurfaceImmersion.Atlas.ChartedUniformMajorants
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAdjustedMean

namespace OAI

/-! A uniform threshold for the actual finite family of transported means.
The profiles, target and their bounds precede the threshold; the map, both
scales, and the actual polynomial solvers follow it. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_family_majorants {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} (p : ι → ChartedMeanProfile P)
    {ρ R : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : ι → Base → ℝ} {K : ι → Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference), (∀ i, (p i).Fits (d i)) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r L
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (chartedFamilyMean d hρ δ q)) β κ := by
  classical
  choose β κ hm using fun i => uniform_charted_majorants (R := R) (p i) hρ q
  refine ⟨(fun m C => 1 + ∑ i, β i m C),(fun m C => 1 + ∑ i, κ i m C),?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  exact MeanBounds.finset_rescaled isOpen_univ.uniqueDiffOn s.coe_nonneg Finset.univ
    (fun i => (d i).mean hρ δ q) (fun _ => tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))
    (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) β κ (fun _ _ => le_rfl)
    (fun i _ => hm i (d i) (hd i) hτ hs hτs hs1 hε hε1 hsmall δ hδ)

theorem uniform_finite_charted_quadratic_mean {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} (p : ι → ChartedMeanProfile P)
    {s : ℝ≥0} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) {ρ R r r₀ : ℝ}
    (hρ : 0 < ρ) (hgap : r₀ < r) (q steps : ℕ)
    {reference H : SmallModes.Base → Tensor} {C : ℕ → ℝ}
    (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ x, ‖H x - reference x‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound Set.univ s m (C m) H) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
      {K : ι → Compacts Base} {ε τ : ℝ}
      {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference), (∀ i, (p i).Fits (d i)) →
      0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ tensorLoss P ≤ η₀ →
      (∀ A, ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
        chartedFamilyLeading d hρ A = A) →
      ∀ δ : ℝ, 0 < δ → ∀ j ≤ steps, ∃ A : SmallModes.Base → Tensor,
        ContDiff ℝ ∞ A ∧ InTrialBall Set.univ reference r A ∧
        (∀ m, WeightedBound Set.univ s m (sizeBound L C β j m) A) ∧
        (∀ m, WeightedBound Set.univ s m
          (δ ^ 2 * (differenceBound L C β κ j m *
            (τ / s + ε / τ ^ tensorLoss P) ^ (j + 1)))
          (combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q A) τ 0 - δ ^ 2 • H)) := by
  obtain ⟨β,κ,hm⟩ := uniform_charted_family_majorants (R := R) p hρ q
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := finite_substitution_uniform (B := β) (K := κ)
    isOpen_univ.uniqueDiffOn s.coe_nonneg hgap hC hH.contDiffOn (fun x _ => hH0 x) hbH steps
  refine ⟨β,κ,η₀,hη₀,hη₁,?_⟩
  intro G hG φ K ε τ c d hd hτ hτs hε hε1 hsmall hdecomp δ hδ j hj
  have hη : 0 < τ / s + ε / τ ^ tensorLoss P :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  obtain ⟨ha,hb,hc,he⟩ := ht _
    (hm d hd hτ hs hτs hs1 hε hε1 (hsmall.trans hη₁) δ hδ) _ hη hsmall j hj
  have ha' : ContDiff ℝ ∞ (fixedTrial H (chartedFamilyMean d hρ δ q) j) :=
    contDiffOn_univ.mp (by simpa only [trial_rescaledMean hη.ne'] using ha)
  have hb' : InTrialBall Set.univ reference r (fixedTrial H (chartedFamilyMean d hρ δ q) j) := by
    simpa only [trial_rescaledMean hη.ne'] using hb
  refine ⟨fixedTrial H (chartedFamilyMean d hρ δ q) j,ha',hb',?_,?_⟩
  · simpa only [trial_rescaledMean hη.ne'] using hc
  · intro m
    apply charted_quadratic_mean_residual d hρ hδ.ne' hτ.ne' q ha' hH (hdecomp _ ha' hb')
    simpa only [trial_rescaledMean hη.ne', rescaledMean_self hη.ne'] using he m

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
