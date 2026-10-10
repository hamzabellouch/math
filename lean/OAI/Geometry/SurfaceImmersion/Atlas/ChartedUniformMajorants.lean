import OAI.Geometry.SurfaceImmersion.Correction.ChartedUniformTrialMean

namespace OAI

/-! Uniform finite-loss majorants for the actual mean operators. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_majorants {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℕ → ℝ → ℝ, ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r L
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (d.mean hρ δ q)) β κ := by
  have hex (m : ℕ) (C : ℝ) := uniform_charted_trial_mean (R := R) p hρ q m C
  choose β κ hβ hκ he using hex
  refine ⟨β,κ,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  have hη : 0 < τ / s + ε / τ ^ tensorLoss P :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  apply rescaledMean_bounds isOpen_univ.uniqueDiffOn hη _ β κ
    (fun m C _ => hβ m C) (fun m C _ => hκ m C)
  · intro A _ _
    exact (c.combinedMeanField δ q (d.amplitude hρ A)).contDiff.contDiffOn
  · intro m C A hC hA hball hb
    have hz : WeightedBound c.e.source s
        (m + (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))) 0 (A - A) := by
      apply (weightedBound_zero c.e.source s _ (F := Tensor)).congr
      intro x _
      exact sub_self (A x)
    exact (he m C d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ A A 0
      (zero_le_one.trans hC) le_rfl
      (hA.mono (Set.subset_univ _)) (hA.mono (Set.subset_univ _))
      (fun x _ => hball x (Set.mem_univ x)) (fun x _ => hball x (Set.mem_univ x))
      (hb.restrict_open c.e.open_source) (hb.restrict_open c.e.open_source) hz).1
  · intro m C D A B hC hD hA hB hballA hballB hbA hbB hbD
    exact (he m C d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ A B D
      (zero_le_one.trans hC) hD (hA.mono (Set.subset_univ _)) (hB.mono (Set.subset_univ _))
      (fun x _ => hballA x (Set.mem_univ x)) (fun x _ => hballB x (Set.mem_univ x))
      (hbA.restrict_open c.e.open_source) (hbB.restrict_open c.e.open_source)
      (hbD.restrict_open c.e.open_source)).2

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
