import OAI.Geometry.SurfaceImmersion.Correction.ChartedMetricMean

namespace OAI

/-! The metric mean difference is linear in the change of the trial
amplitude norm, and retains the same small parameter after chart transport. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem metricMeanField_difference_bound {δ : ℝ} (hδ : 0 < δ)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q m : ℕ) {A N d : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hn : WeightedBound c.e.target s (m + 1 + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap))
    (b b' : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (m + 1 + (q + 1) * (tensorOrder P + 1)) b ≤ A)
    (hb' : supportedWeightedSeminorm c.chartCompact s (m + 1 + (q + 1) * (tensorOrder P + 1)) b' ≤ A)
    (hbb' : supportedWeightedSeminorm c.chartCompact s (m + 1 + (q + 1) * (tensorOrder P + 1)) (b - b') ≤ d) :
    WeightedBound Set.univ s m
      (tensorChartBudget m (c.J m) (c.J (m + 1)) *
        (2 * normalizedMeanBudget (tensorOrder P) c.C c.D q m N * A *
          (τ / s + ε / τ ^ tensorLoss P) * d))
      (fun x => c.metricMeanField δ q b x - c.metricMeanField δ q b' x) := by
  let C := 2 * normalizedMeanBudget (tensorOrder P) c.C c.D q m N * A *
    (τ / s + ε / τ ^ tensorLoss P) * d
  have hM := normalizedMeanBudget_nonneg (tensorOrder P) c.C c.D c.nonnegC q m N
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hv := normalizedMeanBudget_difference δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) hδ hτ hs hτs hs1 hε hsmall
    c.C c.D c.nonnegC c.nonnegD c.coefficients c.operator c.polynomial q m A N hA hN hn b b' d hd hb hb' hbb'
  let f := c.metricMeanFieldInChart δ q b - c.metricMeanFieldInChart δ q b'
  have hfield : WeightedBound Set.univ s m C f :=
    WeightedBound.pi isOpen_univ.uniqueDiffOn hs hC (contDiffOn_pi.mp f.contDiff.contDiffOn)
      (fun k => hv (firstDirection k) (secondDirection k) (firstDirection_norm k) (secondDirection_norm k))
  have hf := supportedSeminorm_le_of_weightedBound hs hC f hfield
  have hD := zero_le_one.trans (c.oneLEJ (m + 1))
  have hcoords := RealModes.weighted_coordDeriv_of_jets c.e.open_source c.smoothForward s.coe_nonneg hs1
    hD (c.coordinates (m + 1))
  have ht := realTensorChartPull_bound c.e c.smoothForward (modeSupport K) c.supportChart
    hs hs1 (c.oneLEJ m) hD (c.coordinates m) hcoords f
  have hT := tensorChartBudget_nonneg m (zero_le_one.trans (c.oneLEJ m)) hD
  have hbound : supportedWeightedSeminorm (modeSupport K) s m
      (realTensorChartPull c.e c.smoothForward (modeSupport K) c.supportChart f) ≤
      tensorChartBudget m (c.J m) (c.J (m + 1)) * C :=
    ht.trans (mul_le_mul_of_nonneg_left hf hT)
  have hout := (weightedBound_of_supportedSeminorm s m
    (realTensorChartPull c.e c.smoothForward (modeSupport K) c.supportChart f)).mono_const hbound
  dsimp only [f] at hout
  rw [realTensorChartPull_sub] at hout
  exact hout

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
