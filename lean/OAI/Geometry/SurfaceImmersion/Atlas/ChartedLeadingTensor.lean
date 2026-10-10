import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamily

namespace OAI

/-! The leading tensors of the actual charted amplitudes are the prescribed
cutoff squares times phase-covector squares. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

lemma chartLeadingTensor_apply (b : SmallModes.Base → ℝ) (e : SmallModes.Base → SmallModes.Base)
    (x : SmallModes.Base) (k : Fin 3) :
    chartLeadingTensor b e x k = b (e x) ^ 2 *
      (fderiv ℝ e x (firstDirection k)).1 * (fderiv ℝ e x (secondDirection k)).1 := by
  change evaluate (fun i => b (e x) ^ 2 * (firstDirection i).1 * (secondDirection i).1)
    (fderiv ℝ e x (firstDirection k)) (fderiv ℝ e x (secondDirection k)) = _
  simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

lemma phase_derivative {x : SmallModes.Base} (hx : x ∈ c.e.source) (v : SmallModes.Base) :
    (fderiv ℝ c.e x v).1 = fderiv ℝ (coordinatePhase φ) x v := by
  have he : (fun y => (c.e y).1) =ᶠ[nhds x] coordinatePhase φ := by
    filter_upwards [c.e.open_source.mem_nhds hx] with y hy using c.phase y hy
  have hd := (c.smoothForward.contDiffAt (c.e.open_source.mem_nhds hx)).differentiableAt (by simp)
  rw [← he.fderiv_eq, fderiv.fst hd]
  rfl

lemma leadingField_apply (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    c.leadingField b x = c.e.source.indicator (fun y k => b (c.e y) ^ 2 *
      fderiv ℝ (coordinatePhase φ) y (firstDirection k) *
      fderiv ℝ (coordinatePhase φ) y (secondDirection k)) x := by
  by_cases hx : x ∈ c.e.source
  · simp only [leadingField, realTensorChartPull_apply, Set.indicator_of_mem hx]
    change chartLeadingTensor b c.e x = _
    ext k
    rw [chartLeadingTensor_apply, c.phase_derivative hx, c.phase_derivative hx]
  · simp only [leadingField, realTensorChartPull_apply, Set.indicator_of_notMem hx]

end PolynomialSolveData

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference)

lemma leading_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) (x : SmallModes.Base) :
    d.leading hρ A x = c.e.source.indicator (fun y k => d.cutoff (c.e y) ^ 2 *
      d.form (c.e y) (A y) * fderiv ℝ (coordinatePhase φ) y (firstDirection k) *
      fderiv ℝ (coordinatePhase φ) y (secondDirection k)) x := by
  change c.leadingField (d.amplitude hρ A) x = _
  rw [c.leadingField_apply]
  by_cases hx : x ∈ c.e.source
  · simp only [Set.indicator_of_mem hx]
    have ha := c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hA.contDiffOn
      (fun y _ => hball y (Set.mem_univ y)) (c.e x)
    have hpos := coefficient_trial_range d.localBounds.invInto d.localBounds.margin
      (fun y _ => hball y (Set.mem_univ y)) (c.e.map_source hx)
    have hn : 0 ≤ coefficient d.form c.e.symm A (c.e x) := hρ.le.trans hpos.1
    have hn' : 0 ≤ d.form (c.e x) (A x) := by
      simpa only [coefficient, c.e.left_inv hx] using hn
    ext k
    change c.trialAmplitude d.cutoff d.form d.localBounds hρ A (c.e x) ^ 2 * _ * _ = _
    rw [ha]
    simp only [phaseAmplitude, mul_pow, coefficient, c.e.left_inv hx, Real.sq_sqrt hn']
  · simp only [Set.indicator_of_notMem hx]

end ChartedMeanData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
