import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusin
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingDiagonal

namespace OAI

/-!
# Joint almost-everywhere leaf covariance for the shearing flow

The fixed-time covariance theorem alone does not justify using a time
selected from a recurrence argument. Measurable kernels and a countable
determining family of leaf tests allow Fubini to put the time quantifier
inside: almost every initial point has covariance at almost every real
time. This is sufficient for selection after finitely many affine time
changes, without asserting an unproved pointwise equivariant version.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rescaledRealKernel {Y : Type*} [MeasurableSpace Y]
    (κ : Kernel Y ℝ) [IsSFiniteKernel κ] (c : Y → ℝ) (hc : Measurable c) :
    Kernel Y ℝ where
  toFun y := (κ y).map (fun u => c y * u)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := κ)
      (((hc.comp measurable_fst).mul measurable_snd) hS)
    convert H using 1
    funext y
    exact Measure.map_apply (measurable_const.mul measurable_id) hS

def normalizedRescaledRealKernel {Y : Type*} [MeasurableSpace Y]
    (κ : Kernel Y ℝ) [IsSFiniteKernel κ] (c : Y → ℝ) (hc : Measurable c) :
    Kernel Y ℝ where
  toFun y := anchorNormalize (rescaledRealKernel κ c hc y) (Metric.ball 0 1)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    exact ((rescaledRealKernel κ c hc).measurable_coe
      Metric.isOpen_ball.measurableSet).inv.mul
        ((rescaledRealKernel κ c hc).measurable_coe hS)

lemma normalized_scaling_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r)) (c : ℝ) (hc : 0 < c) :
    IsLocallyFiniteMeasure
      (anchorNormalize (ν.map (fun u => c * u)) (Metric.ball 0 1)) := by
  have hm : ν.map (fun u => c * u) (Metric.ball 0 1) = ν (Metric.ball 0 (1 / c)) := by
    rw [Measure.map_apply (show Measurable (fun u : ℝ => c * u) from by fun_prop)
      Metric.isOpen_ball.measurableSet]
    exact congrArg ν (realScaling_preimage_ball c 1 hc)
  apply locallyFinite_of_finite_real_windows
  intro m
  change (ν.map (fun u => c * u) (Metric.ball 0 1))⁻¹ *
    ν.map (fun u => c * u) (Icc (-(m : ℝ)) m) < ∞
  rw [hm, Measure.map_apply (show Measurable (fun u : ℝ => c * u) from by fun_prop)
    measurableSet_Icc]
  apply ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (hp _ (by positivity)))
  exact ((Homeomorph.mulLeft₀ c hc.ne').isCompact_preimage.mpr isCompact_Icc).measure_lt_top

def rootPairCovarianceKernel
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (X n × ℝ) ℝ :=
  normalizedRescaledRealKernel (Kernel.prodMkRight ℝ (intrinsicRootKernel hij μ hfree))
    (fun p => Real.exp (-2 * p.2)) (by fun_prop)

lemma rootPairCovarianceKernel_apply
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x : X n) (t : ℝ) :
    rootPairCovarianceKernel hij μ hfree (x, t) =
      anchorNormalize ((intrinsicRootKernel hij μ hfree x).map
        (fun u => Real.exp (-2 * t) * u)) (Metric.ball 0 1) := rfl

theorem ae_rootPairKernel_covariance_fixed
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree (rightAction x (rootPairFlow i j (-t))) =
      rootPairCovarianceKernel hij μ hfree (x, t) := by
  have hpres := rootPairFlow_preserving d i j (-t) μ hA
  have hmap : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootPairFlow i j (-t))),
      intrinsicRootKernel hij μ hfree y = intrinsicRootLeaf hij μ y := by
    rw [hpres.map_eq]
    exact ae_intrinsicRootKernel_eq hij μ hfree
  have htarget := ae_of_ae_map hpres.measurable.aemeasurable hmap
  have hcov := ae_intrinsicRootLeaf_diagonal hij (rootPairWeights i j)
    (rootPairWeights_sum i j) (-t) μ hfree hpres.map_eq
  have hs : rootTimeScaling (rootPairWeights i j) i j (-t) =
      Homeomorph.mulLeft₀ (Real.exp (-2 * t)) (Real.exp_ne_zero _) := by
    ext u
    simp only [rootTimeScaling, Homeomorph.coe_mulLeft₀,
      rootPairWeights_row hij, rootPairWeights_col hij]
    congr 2
    ring
  filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree, htarget, hcov] with x hx ht hc
  rw [ht, rootPairCovarianceKernel_apply, hx]
  simpa only [rootPairFlow, hs, Homeomorph.coe_mulLeft₀] using hc

theorem ae_rootPairKernel_covariance_time
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ t : ℝ ∂volume,
      intrinsicRootKernel hij μ hfree (rightAction x (rootPairFlow i j (-t))) =
        rootPairCovarianceKernel hij μ hfree (x, t) := by
  let κ := intrinsicRootKernel hij μ hfree
  let η := rootPairCovarianceKernel hij μ hfree
  let η' := locallyFiniteRealVersion η
  have hflow : Measurable (fun p : X (d + 1) × ℝ =>
      rightAction p.1 (rootPairFlow i j (-p.2))) := by
    apply Continuous.measurable
    exact (continuous_rightAction_uncurry (d + 1)).comp
      (continuous_fst.prodMk ((continuous_diagonalOneParameter
        (rootPairWeights i j) (rootPairWeights_sum i j)).comp continuous_snd.neg))
  have hmeas : MeasurableSet {p : X (d + 1) × ℝ |
      κ (rightAction p.1 (rootPairFlow i j (-p.2))) = η' p} := by
    simp_rw [realMeasures_eq_iff_leafTests]
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    exact measurableSet_eq_fun
      (((leafTest a b).continuous.stronglyMeasurable.integral_kernel.measurable).comp hflow)
      (leafTest a b).continuous.stronglyMeasurable.integral_kernel.measurable
  have hfixed (t : ℝ) : ∀ᵐ x ∂μ,
      κ (rightAction x (rootPairFlow i j (-t))) = η' (x, t) := by
    filter_upwards [ae_rootPairKernel_covariance_fixed d hij μ hA hfree t] with x hx
    have hloc : IsLocallyFiniteMeasure (η (x, t)) := hx ▸ inferInstance
    rw [show η' (x, t) = η (x, t) from locallyFiniteRealVersion_eq η (x, t)]
    exact hx
  have htime : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ ∂volume,
      κ (rightAction x (rootPairFlow i j (-t))) = η' (x, t) :=
    (MeasureTheory.Measure.ae_ae_comm hmeas).mpr (Eventually.of_forall hfixed)
  filter_upwards [htime, ae_intrinsicRootKernel_eq hij μ hfree,
    ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx he hp
  have hpos : ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    simpa only [κ, he] using hp
  filter_upwards [hx] with t ht
  have hloc : IsLocallyFiniteMeasure (η (x, t)) :=
    normalized_scaling_locallyFinite (κ x) hpos (Real.exp (-2 * t)) (Real.exp_pos _)
  exact ht.trans (locallyFiniteRealVersion_eq η (x, t))

end DukePrimeDegree

end

end OAI
