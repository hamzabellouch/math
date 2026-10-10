import OAI.Geometry.SurfaceImmersion.Atlas.ChartedTrialAmplitude

namespace OAI

/-! The actual trial-tensor mean map used by finite substitution. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

def trialMean (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    SmallModes.Base → Tensor := c.combinedMeanField δ q (c.trialAmplitude ψ Q h hρ A)

theorem trialMean_estimates
    (d : Budgets c.e.source c.e.target s c.realMap ψ Q c.e c.e.symm)
    (hρ : 0 < ρ) {Q₀ : Set LowJet} (hQ : IsCompact Q₀) (hQO : Q₀ ⊆ c.O)
    (q m : ℕ) (C B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (hGQ : Set.MapsTo (lowJet G) c.U Q₀)
    (hGb : WeightedBound c.U s (m + tensorOrder P) B (lowJet G))
    (hφb : ∀ v, WeightedBound c.U s (m + tensorOrder P) F
      (fun x => fderiv ℝ φ x (coordinateVector v))) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℝ, 1 ≤ β ∧ 1 ≤ κ ∧ ∀ δ : ℝ, 0 < δ →
      ∀ (A B : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A c.e.source → ContDiffOn ℝ ∞ B c.e.source →
      InTrialBall c.e.source reference r A → InTrialBall c.e.source reference r B →
      WeightedBound c.e.source s (m + L) C A → WeightedBound c.e.source s (m + L) C B →
      WeightedBound c.e.source s (m + L) D (A - B) →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * β)
        (c.trialMean ψ Q h hρ δ q A) ∧
      WeightedBound Set.univ s m (κ * (τ / s + ε / τ ^ tensorLoss P) * D)
        (c.trialMean ψ Q h hρ δ q A - c.trialMean ψ Q h hρ δ q B) := by
  let j := m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
  obtain ⟨A₀,hA₀,ha⟩ := c.trialAmplitude_bounds ψ Q h d hs hs1 hρ j C
  have hA0 : 0 ≤ A₀ := zero_le_one.trans hA₀
  have hN : 0 ≤ d.normal j := zero_le_one.trans (d.normal_pos j)
  obtain ⟨E,hE,he⟩ := c.combined_mean_bounds hQ hQO q m B F A₀ (d.normal j) hB hF hA0 hN
    hτ hs hτs hs1 hε hε1 hsmall hGQ hGb hφb (d.normal_bound j)
  refine ⟨max 1 E, max 1 (2 * E * inputFactor d j), le_max_left _ _, le_max_left _ _, ?_⟩
  intro δ hδ A B D hC hD hA hB hballA hballB hbA hbB hbD
  have hj : m + (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) = j := by dsimp [j]; omega
  rw [hj] at hbA hbB hbD
  obtain ⟨hu,hv,hd⟩ := ha A B D hC hD hA hB hballA hballB hbA hbB hbD
  have hz : 0 ≤ inputFactor d j * D := mul_nonneg (inputFactor_nonneg d j) hD
  have hdiff : supportedWeightedSeminorm c.chartCompact s j
      (c.trialAmplitude ψ Q h hρ A - c.trialAmplitude ψ Q h hρ B) ≤ A₀ * (inputFactor d j * D) := by
    simpa only [mul_assoc] using hd
  have hh := he δ hδ _ _ (inputFactor d j * D) hz hu hv hdiff
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  constructor
  · exact hh.1.mono_const (mul_le_mul_of_nonneg_left (le_max_right _ _) hη)
  · apply hh.2.mono_const
    calc
      _ = (2 * E * inputFactor d j) * (τ / s + ε / τ ^ tensorLoss P) * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hη) hD

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
