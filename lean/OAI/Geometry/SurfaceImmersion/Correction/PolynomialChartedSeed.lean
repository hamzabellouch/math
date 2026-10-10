import OAI.Geometry.SurfaceImmersion.Correction.PolynomialTrialAmplitude
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMetricFreeBudgets
import OAI.Geometry.SurfaceImmersion.Correction.ChartedUniformFree

namespace OAI

/-! Actual slow-scale complex amplitudes with polynomial geometric and input budgets. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem polynomial_charted_seed_bounds (q m : ℕ) :
    ∃ p : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0}
      {c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      (∀ j, c.D j = 0) → ∀ hρ : 0 < ρ,
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.budgets.inv (m+q+1) ≤ B → d.budgets.forms (m+q+1) ≤ B →
      d.budgets.psi (m+q+1) ≤ B →
      ∀ N : ℕ → ℝ, (∀ j, 0 ≤ N j) → d.budgets.normal (m+q+1) ≤ N (m+q+1) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ f : SmallModes.Base → Tensor,
      ContDiff ℝ ∞ f → InTrialBall univ reference r f →
      WeightedBound univ s (m+q+1) B f →
      WeightedBound univ s m
        (metricFreeSizeBudget c.C c.J N q m*(A*B^p)*(δ*τ))
        (d.freeAmplitude hρ δ q f) := by
  obtain ⟨p,A,hA,hamp⟩ := polynomial_trial_amplitude_bounds (m+q+1)
  refine ⟨p,A,hA,?_⟩
  intro τ G hG φ K s c r ρ R reference d hD hρ hτ hs hτs hs1 B hB hρB hi hf hp N hN hn δ hδ f hfs hfb hbf
  have hz : WeightedBound c.e.source s (m+q+1) 0 (f-f) := by
    apply (weightedBound_zero c.e.source s (m+q+1) (F := Tensor)).congr
    intro x _
    exact sub_self (f x)
  have hball : InTrialBall c.e.source reference r f := fun x _ => hfb x (mem_univ x)
  have ha := (hamp d hρ hs hs1 B hB hρB hi hf hp f f 0 le_rfl hfs.contDiffOn hfs.contDiffOn
    hball hball (hbf.restrict_open c.e.open_source) (hbf.restrict_open c.e.open_source) hz).1
  have hj : PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m = m+q+1 := by
    simp only [PolynomialSolveData.inputOrder,tensorOrder_emptyMetricPolynomial,Nat.zero_add,Nat.mul_one]
    omega
  have ha' : supportedWeightedSeminorm c.chartCompact s
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (d.amplitude hρ f) ≤ A*B^p := by
    simpa only [hj] using ha
  have hn' : WeightedBound c.e.target s
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (N (m+q+1)) (freeNormal c.realMap) := by
    rw [hj]
    exact (d.budgets.normal_bound (m+q+1)).mono_const hn
  have hAp : 0 ≤ A*B^p := mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans hB) _)
  have hsmall : τ/s + (0 : ℝ)/τ^tensorLoss emptyMetricPolynomial ≤ 1 := by
    simp only [zero_div,add_zero]
    exact (div_le_one₀ hs).mpr hτs
  have hb := c.originalFreeSeed_bound hδ hτ hs hτs hs1 le_rfl hsmall q m
    hAp (hN _) hn' (d.amplitude hρ f) ha'
  have hbudget := correctedSeedBudget_nonneg (tensorOrder emptyMetricPolynomial)
    c.C c.D c.nonnegC q m (hN (m+q+1))
  have htwo : (1 : ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
  have hJ : 0 ≤ c.J m^m := pow_nonneg (zero_le_one.trans (c.oneLEJ m)) _
  have hcoeff : (m.factorial : ℝ) * c.J m^m *
      correctedSeedBudget (tensorOrder emptyMetricPolynomial) c.C c.D q m (N (m+q+1)) ≤
      c.freeSizeFactor q m (N (m+q+1)) := by
    calc
      _ = (m.factorial : ℝ) * 1 *
          correctedSeedBudget (tensorOrder emptyMetricPolynomial) c.C c.D q m (N (m+q+1)) *
          c.J m^m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)) hbudget) hJ
  rw [c.metric_freeSizeFactor_eq hD N q m] at hcoeff
  apply (weightedBound_of_supportedSeminorm s m (d.freeAmplitude hρ δ q f)).mono_const
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff hAp) (mul_nonneg hδ hτ.le))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
