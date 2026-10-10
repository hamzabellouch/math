import OAI.Geometry.SurfaceImmersion.Correction.ChartedFiniteMean

namespace OAI

/-! The actual original-coordinate quadratic mean after finite substitution.
The threshold in this statement still concerns fixed scale data. -/
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

lemma chartedFamilyMean_smooth (hρ : 0 < ρ) (δ : ℝ) (q : ℕ)
    (A : SmallModes.Base → Tensor) : ContDiff ℝ ∞ (chartedFamilyMean d hρ δ q A) :=
  ContDiff.sum (fun i _ => ((c i).combinedMeanField δ q ((d i).amplitude hρ A)).contDiff)

lemma charted_quadratic_mean_residual (hρ : 0 < ρ) {δ : ℝ}
    (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) {A H : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H)
    (hdecomp : chartedFamilyLeading d hρ A = A) {m : ℕ} {C : ℝ}
    (hb : WeightedBound Set.univ s m C (A + chartedFamilyMean d hρ δ q A - H)) :
    WeightedBound Set.univ s m (δ ^ 2 * C)
      (combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q A) τ 0 - δ ^ 2 • H) := by
  have hh := hb.const_smul isOpen_univ.uniqueDiffOn
    ((hA.add (chartedFamilyMean_smooth d hρ δ q A)).sub hH).contDiffOn (δ ^ 2)
  rw [abs_of_nonneg (sq_nonneg δ)] at hh
  apply hh.congr
  intro x _
  rw [charted_family_zero_phase_identity d hρ hδ hτ q A, hdecomp]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_sub]

theorem finite_charted_adjusted_quadratic_mean (hρ : 0 < ρ) (hτ : 0 < τ)
    (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q steps : ℕ)
    {H : SmallModes.Base → Tensor} {r₀ : ℝ} (hgap : r₀ < r)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ x, ‖H x - reference x‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound Set.univ s m (C m) H)
    (hdecomp : ∀ A, ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      chartedFamilyLeading d hρ A = A) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → τ / s + ε / τ ^ tensorLoss P ≤ η₀ →
      ∀ j ≤ steps, ∃ A : SmallModes.Base → Tensor, ContDiff ℝ ∞ A ∧
        InTrialBall Set.univ reference r A ∧
        (∀ m, WeightedBound Set.univ s m (sizeBound L C β j m) A) ∧
        (∀ m, WeightedBound Set.univ s m
          (δ ^ 2 * (differenceBound L C β κ j m *
            (τ / s + ε / τ ^ tensorLoss P) ^ (j + 1)))
          (combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q A) τ 0 - δ ^ 2 • H)) := by
  obtain ⟨β,κ,η₀,hη₀,hη₁,ht⟩ := finite_charted_mean_adjustment d hρ hτ hs hτs hs1
    hε hε1 hsmall q steps hgap hC hH hH0 hbH
  refine ⟨β,κ,η₀,hη₀,hη₁,?_⟩
  intro δ hδ hη j hj
  obtain ⟨ha,hb,hc,hd⟩ := ht δ hδ hη j hj
  refine ⟨fixedTrial H (chartedFamilyMean d hρ δ q) j,ha,hb,hc,?_⟩
  intro m
  exact charted_quadratic_mean_residual d hρ hδ.ne' hτ.ne' q ha hH (hdecomp _ ha hb) (hd m)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
