import OAI.Geometry.SurfaceImmersion.Correction.ChartedZeroMean
import OAI.Geometry.SurfaceImmersion.Atlas.RealTensorChart
import OAI.Geometry.SurfaceImmersion.Correction.CombinedMeanGeometry

namespace OAI

/-! Global supported metric mean fields for the actual charted free seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes JetPolynomial
lemma normalizedPerturbedMean_smooth_general {F : RField 4} {U : Set SmallModes.Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts SmallModes.Base)
    (hKU : (K : Set SmallModes.Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (δ τ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) K) (v w : SmallModes.Base) :
    ContDiff ℝ ∞ (normalizedPerturbedMean δ τ hF h K hKU R q b v w) :=
  (seedMeanError_smooth τ (perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q)
    (supportedFreeSeed δ τ hF h K hKU b) (supportedFreeSeed δ τ hF h K hKU b) v w).const_smul (δ⁻¹ ^ 2)
end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def metricMeanFieldInChart (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) c.chartCompact :=
  ⟨c.metricMeanInChart δ q b,
    contDiff_pi.mpr (fun k => normalizedPerturbedMean_smooth_general c.smoothMap c.realDomain
      c.chartCompact (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator δ τ q b
      (firstDirection k) (secondDirection k)),
    fun y hy => by
      ext k
      change δ⁻¹ ^ 2 * SmallModes.seedMeanError τ _ _ _ (firstDirection k) (secondDirection k) y = 0
      rw [SmallModes.seedMeanError_zero_outside τ c.chartCompact _ _ _ _ _ _ hy, mul_zero]⟩

def metricMeanField (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) (modeSupport K) :=
  realTensorChartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.metricMeanFieldInChart δ q b)

lemma metricMeanField_apply (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact)
    (x : SmallModes.Base) :
    c.metricMeanField δ q b x = c.e.source.indicator
      (fun x => pullbackField c.e x (c.metricMeanInChart δ q b (c.e x))) x := rfl

theorem metricMeanField_bound {δ : ℝ} (hδ : 0 < δ)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q m : ℕ) {A N : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hn : WeightedBound c.e.target s (m + 1 + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap))
    (b : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (m + 1 + (q + 1) * (tensorOrder P + 1)) b ≤ A) :
    WeightedBound Set.univ s m
      (tensorChartBudget m (c.J m) (c.J (m + 1)) *
        ((τ / s + ε / τ ^ tensorLoss P) * (normalizedMeanBudget (tensorOrder P) c.C c.D q m N * A ^ 2)))
      (c.metricMeanField δ q b) := by
  let C := (τ / s + ε / τ ^ tensorLoss P) * (normalizedMeanBudget (tensorOrder P) c.C c.D q m N * A ^ 2)
  have hC : 0 ≤ C := mul_nonneg
    (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _)))
    (mul_nonneg (normalizedMeanBudget_nonneg (tensorOrder P) c.C c.D c.nonnegC q m N) (sq_nonneg A))
  have hv := normalizedMeanBudget_bound δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) hδ hτ hs hτs hs1 hε hsmall
    c.C c.D c.nonnegC c.nonnegD c.coefficients c.operator c.polynomial q m A N hA hN hn b hb
  have hfield : WeightedBound Set.univ s m C (c.metricMeanFieldInChart δ q b) :=
    WeightedBound.pi isOpen_univ.uniqueDiffOn hs hC
      (contDiffOn_pi.mp (c.metricMeanFieldInChart δ q b).contDiff.contDiffOn)
      (fun k => hv (firstDirection k) (secondDirection k) (firstDirection_norm k) (secondDirection_norm k))
  have hf := supportedSeminorm_le_of_weightedBound hs hC (c.metricMeanFieldInChart δ q b) hfield
  have hD := zero_le_one.trans (c.oneLEJ (m + 1))
  have hcoords := RealModes.weighted_coordDeriv_of_jets c.e.open_source c.smoothForward s.coe_nonneg hs1
    hD (c.coordinates (m + 1))
  have ht := realTensorChartPull_bound c.e c.smoothForward (modeSupport K) c.supportChart
    hs hs1 (c.oneLEJ m) hD (c.coordinates m) hcoords (c.metricMeanFieldInChart δ q b)
  have hT := tensorChartBudget_nonneg m (zero_le_one.trans (c.oneLEJ m)) hD
  have hbound : supportedWeightedSeminorm (modeSupport K) s m (c.metricMeanField δ q b) ≤
      tensorChartBudget m (c.J m) (c.J (m + 1)) * C :=
    ht.trans (mul_le_mul_of_nonneg_left hf hT)
  exact (weightedBound_of_supportedSeminorm s m (c.metricMeanField δ q b)).mono_const hbound

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
