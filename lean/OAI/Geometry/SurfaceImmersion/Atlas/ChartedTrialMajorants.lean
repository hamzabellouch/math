import OAI.Geometry.SurfaceImmersion.Correction.ChartedTrialMean
import OAI.Geometry.SurfaceImmersion.Correction.FixedMeanSubstitution

namespace OAI

/-! The actual charted trial mean satisfies the finite-substitution
interface, with majorants chosen before the amplitude scale. -/
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

theorem trialMean_majorants
    (d : Budgets c.e.source c.e.target s c.realMap ψ Q c.e c.e.symm)
    (hρ : 0 < ρ) {Q₀ : Set LowJet} (hQ : IsCompact Q₀) (hQO : Q₀ ⊆ c.O)
    (q : ℕ) (B F : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (hGQ : Set.MapsTo (lowJet G) c.U Q₀)
    (hGb : ∀ m, WeightedBound c.U s (m + tensorOrder P) (B m) (lowJet G))
    (hφb : ∀ m v, WeightedBound c.U s (m + tensorOrder P) (F m)
      (fun x => fderiv ℝ φ x (coordinateVector v))) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r L
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (c.trialMean ψ Q h hρ δ q)) β κ := by
  have hex (m : ℕ) (C : ℝ) := c.trialMean_estimates ψ Q h d hρ hQ hQO q m C (B m) (F m)
    (hB m) (hF m) hτ hs hτs hs1 hε hε1 hsmall hGQ (hGb m) (hφb m)
  choose β κ hβ hκ he using hex
  refine ⟨β,κ,?_⟩
  intro δ hδ
  have hη : 0 < τ / s + ε / τ ^ tensorLoss P :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  apply rescaledMean_bounds isOpen_univ.uniqueDiffOn hη _ β κ
    (fun m C _ => hβ m C) (fun m C _ => hκ m C)
  · intro A _ _
    exact (c.combinedMeanField δ q (c.trialAmplitude ψ Q h hρ A)).contDiff.contDiffOn
  · intro m C A hC hA hball hb
    have hz : WeightedBound c.e.source s
        (m + (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))) 0 (A - A) := by
      apply (weightedBound_zero c.e.source s _ (F := Tensor)).congr
      intro x _
      exact sub_self (A x)
    exact (he m C δ hδ A A 0 (zero_le_one.trans hC) le_rfl
      (hA.mono (Set.subset_univ _)) (hA.mono (Set.subset_univ _))
      (fun x _ => hball x (Set.mem_univ x)) (fun x _ => hball x (Set.mem_univ x))
      (hb.restrict_open c.e.open_source) (hb.restrict_open c.e.open_source) hz).1
  · intro m C D A B hC hD hA hB hballA hballB hbA hbB hbD
    exact (he m C δ hδ A B D (zero_le_one.trans hC) hD
      (hA.mono (Set.subset_univ _)) (hB.mono (Set.subset_univ _))
      (fun x _ => hballA x (Set.mem_univ x)) (fun x _ => hballB x (Set.mem_univ x))
      (hbA.restrict_open c.e.open_source) (hbB.restrict_open c.e.open_source)
      (hbD.restrict_open c.e.open_source)).2

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
