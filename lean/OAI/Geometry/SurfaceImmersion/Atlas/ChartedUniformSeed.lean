import OAI.Geometry.SurfaceImmersion.Correction.ChartedUniformFree

namespace OAI

/-! Uniform slow-scale bounds for the original-coordinate free amplitudes,
as required by the quadratic target estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_seed_bound {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ s m (B * (δ * τ)) (d.freeAmplitude hρ δ q A) := by
  let j := PolynomialSolveData.inputOrder (P := P) q m
  obtain ⟨A₀,hA₀,ha⟩ := uniform_charted_trial_amplitude (R := R) p.openV hρ j C
    (p.inv j) (p.forms j) (p.psi j) (p.oneLEInv j) (p.oneLEForms j) (p.oneLEPsi j)
  let B₀ := (m.factorial : ℝ) * p.J m ^ m *
    correctedSeedBudget (tensorOrder P) p.C p.D q m (p.normal j)
  refine ⟨max 1 (B₀ * A₀),le_max_left _ _,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  have hz : WeightedBound c.e.source s j 0 (A - A) := by
    apply (weightedBound_zero c.e.source s j (F := Tensor)).congr
    intro x _
    exact sub_self (A x)
  obtain ⟨hu,_,_⟩ := ha c d.cutoff d.form d.localBounds d.budgets hd.target
    (congrFun hd.inverse j) (congrFun hd.forms j) (congrFun hd.cutoff j) hs hs1
    A A 0 hC le_rfl hA.contDiffOn hA.contDiffOn
    (fun x _ => hball x (Set.mem_univ x)) (fun x _ => hball x (Set.mem_univ x))
    (hbA.restrict_open c.e.open_source) (hbA.restrict_open c.e.open_source) hz
  have hn : WeightedBound c.e.target s j (p.normal j) (freeNormal c.realMap) := by
    simpa only [hd.normal] using d.budgets.normal_bound j
  have hb := c.originalFreeSeed_bound hδ hτ hs hτs hs1 hε hsmall q m
    (zero_le_one.trans hA₀) (zero_le_one.trans (p.oneLENormal j)) hn (d.amplitude hρ A) hu
  have hb' : supportedWeightedSeminorm K s m (d.freeAmplitude hρ δ q A) ≤
      B₀ * A₀ * (δ * τ) := by
    simpa only [ChartedMeanData.freeAmplitude,hd.coefficients,hd.perturbation,hd.coordinates,B₀] using hb
  exact ((weightedBound_of_supportedSeminorm s m (d.freeAmplitude hρ δ q A)).mono_const hb').mono_const
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
