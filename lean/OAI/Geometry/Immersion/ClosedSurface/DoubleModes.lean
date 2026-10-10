import OAI.Geometry.Immersion.ClosedSurface.MetricTensors

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realOsc_neg {n : ℕ} (τ : ℝ) (Z : Field n) :
    realOsc τ (fun p => -Z p) = fun p => -realOsc τ Z p := by
  funext p i
  simp [realOsc, QuadraticMean.realPart, oscillate]

lemma realLinearized_add_right {n : ℕ} {F X Y : RField n} {p : Base}
    (hX : DifferentiableAt ℝ X p) (hY : DifferentiableAt ℝ Y p) (v w : Base) :
    realLinearized F (fun q => X q + Y q) v w p =
      realLinearized F X v w p + realLinearized F Y v w p := by
  simp only [realLinearized, partial_add hX hY, dotProduct_add]
  ring

lemma realMetricTensor_add {n : ℕ} {F X : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hX : DifferentiableAt ℝ X p) :
    realMetricTensor (fun q => F q + X q) p =
      realMetricTensor F p + realLinearizedTensor F X p + realMetricTensor X p := by
  ext i
  simp only [Pi.add_apply, realMetricTensor_apply, realLinearizedTensor_apply,
    realMetric_add hF hX]


lemma single_phase_metric_identity {n : ℕ} {F : RField n} {Z W : Field n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p)
    (hW : DifferentiableAt ℝ W p) (τ : ℝ) :
    realMetricTensor (fun q => F q + (realOsc τ Z q + realOsc (τ / 2) W q)) p -
        realMetricTensor F p - zeroTensor τ Z p =
      realLinearizedTensor F (realOsc τ Z) p +
      (realLinearizedTensor F (realOsc (τ / 2) W) p +
        realOsc (τ / 2) (doubleTensor τ Z) p) +
      (realLinearizedTensor (realOsc τ Z) (realOsc (τ / 2) W) p +
        realMetricTensor (realOsc (τ / 2) W) p) := by
  have hd (σ : ℝ) {A : Field n} (ha : DifferentiableAt ℝ A p) :
      DifferentiableAt ℝ (realOsc σ A) p := by
    have hO : DifferentiableAt ℝ (oscillate σ A) p := by
      unfold oscillate
      exact (unitMode_hasFDerivAt σ p).differentiableAt.smul ha
    exact ((QuadraticMean.realPartCLM n).differentiableAt).comp p hO
  have hu := hd τ hZ
  have hv := hd (τ / 2) hW
  have huv : DifferentiableAt ℝ (fun q => realOsc τ Z q + realOsc (τ / 2) W q) p := hu.add hv
  rw [realMetricTensor_add hF huv, realMetricTensor_add hu hv,
    realMetric_realOsc hZ]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, realLinearizedTensor_apply,
    realLinearized_add_right hu hv]
  ring



def doubleCancelAmplitude {n : ℕ} (τ : ℝ) (F : RField n) (Z : Field n) (q : ℕ) : Field n :=
  modeApprox (τ / 2) (fun p => complexify (F p)) (fun _ => 0)
    (fun p => -doubleTensor τ Z p) q

def doubleCancelField {n : ℕ} (τ : ℝ) (F : RField n) (Z : Field n) (q : ℕ) : RField n :=
  realOsc (τ / 2) (doubleCancelAmplitude τ F Z q)

theorem weighted_doubleCanceller {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (h : ModeDomain (fun p => complexify (F p)) U)
    {Z : Field n} {τ s K C : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C) (hZ : ContDiffOn ℝ ∞ Z U) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 1) K)
    (hb : WeightedBound U s (m + q + 2) C Z) :
    let D := (n : ℝ) * (2 ^ (m + q + 1) * (2 * C / τ) * (2 * C / τ))
    ContDiffOn ℝ ∞ (doubleCancelField τ F Z q) U ∧
    WeightedBound U τ m (2 ^ m * (2 ^ m * (forcedModeConstant n m K q * D)))
      (doubleCancelField τ F Z q) ∧
    WeightedBound U τ m
      (2 ^ m * (2 ^ m * (fullErrorConstant n (m + q) K ^ (q + 1) *
        (τ / 2 / s) ^ (q + 1) * D)))
      (fun p => realLinearizedTensor F (doubleCancelField τ F Z q) p +
        realOsc (τ / 2) (doubleTensor τ Z) p) := by
  dsimp only
  have hdt := contDiffOn_doubleTensor h.isOpen hZ τ
  have hτ2 : 0 < τ / 2 := by positivity
  have hτ2s : τ / 2 ≤ s := by linarith
  have hbd' : WeightedBound U s (m + q + 1 + 1) C Z := by
    exact hb
  have hbd := weighted_doubleTensor h.isOpen hτ hs hτs hC hZ hbd'
  have hD : 0 ≤ (n : ℝ) * (2 ^ (m + q + 1) * (2 * C / τ) * (2 * C / τ)) := by positivity
  have hh := real_finite_forced_mode hF h hτ2 hs hτ2s hs1 hK hD hdt.neg q m hc
    (hbd.neg h.isOpen.uniqueDiffOn hdt)
  dsimp only at hh
  rcases hh with ⟨hsmooth, hbound, herror⟩
  have hFM := forcedModeConstant_nonneg n m q hK
  have hFE := fullErrorConstant_nonneg n (m + q) hK
  have hb' := hbound.enlarge_scale (by positivity) (c := 2) (by norm_num)
  have he' := herror.enlarge_scale (by positivity) (c := 2) (by norm_num)
  have heq : 2 * (τ / 2) = τ := by ring
  rw [heq] at hb' he'
  refine ⟨hsmooth, hb', ?_⟩
  apply he'.congr
  intro p hp
  simp only [doubleCancelField, doubleCancelAmplitude, realOsc_neg, sub_neg_eq_add]

end ClosedSurfaceR4.RealModes

end

end OAI
