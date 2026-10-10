import Mathlib
import OAI.Probability.Subsphere.Regression.Gaussian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def matrixLabelReference (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  (Measure.pi (fun _ => stdGaussian E)).prod volume

def projectionLaw (ν : Measure E) (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  ((Measure.pi (fun _ => stdGaussian E)).prod ν).map
    (fun z => (z.1, fun j => ⟪z.2, z.1 j⟫))

def gaussianCoupling (ν : Measure E) (m : ℕ) :
    Measure ((Fin m → E) × (E × (Fin m → ℝ))) :=
  (Measure.pi (fun _ => stdGaussian E)).prod
    (ν.prod (Measure.pi (fun _ => gaussianReal 0 1)))

def noisyObservation (m : ℕ) (δ : ℝ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) : (Fin m → E) × (Fin m → ℝ) :=
  (z.1, fun j => ⟪z.2.1, z.1 j⟫ + δ * z.2.2 j)

lemma measurable_noisyObservation (m : ℕ) (δ : ℝ) :
    Measurable (noisyObservation (E := E) m δ) := by
  unfold noisyObservation
  fun_prop

lemma gaussianCoupling_map_noisyObservation_zero (ν : Measure E) [SigmaFinite ν] (m : ℕ) :
    (gaussianCoupling ν m).map (noisyObservation m 0) = projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m 0),
    projectionLaw, lintegral_map hf (by fun_prop)]
  dsimp [gaussianCoupling, noisyObservation]
  simp only [zero_mul, add_zero]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  simp

/-- The smoothed projection really is the density of the coupled noisy law. -/
lemma gaussianCoupling_map_noisyObservation (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    (gaussianCoupling ν m).map (noisyObservation m δ) =
      (matrixLabelReference (E := E) m).withDensity
        (projectionSmoothing ν (gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ))) m) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m δ),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hf]
  dsimp [gaussianCoupling, matrixLabelReference, noisyObservation]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by
    exact ((measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _).mul hf).aemeasurable)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  have he (p : E) := lintegral_gaussian_shift_scale m δ hδ
    (fun j => ⟪p, A j⟫) (fun y => f (A, y)) (hf.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [lintegral_mul_const _ (by fun_prop)]
  rfl
lemma matrixLabelReference_outerRegular (m : ℕ) :
    (matrixLabelReference (E := E) m).OuterRegular := by
  unfold matrixLabelReference
  exact (Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite
    ((Measure.pi (fun _ : Fin m => stdGaussian E)).prod volume)).toOuterRegular

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_noisyObservation (m : ℕ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) :
    Tendsto (fun k : ℕ => noisyObservation m (1 / ((k : ℝ) + 1)) z)
      atTop (𝓝 (noisyObservation m 0 z)) := by
  apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)

theorem projectionLaw_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hn : 1 ≤ n) (hmargin : (n : ℝ) + m ≤ a)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤
      (ν Set.univ * (replicaConstant ν a m)^n)^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by
  have hp : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  have hC : ν Set.univ * (replicaConstant ν a m)^n ≠ ∞ := by
    unfold replicaConstant
    finiteness
  have := matrixLabelReference_outerRegular (E := E) m
  apply measure_apply_le_of_isOpen _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hα
  intro U hU
  rw [← gaussianCoupling_map_noisyObservation_zero ν m]
  apply map_apply_open_le_of_tendsto (gaussianCoupling ν m)
    (matrixLabelReference (E := E) m) (noisyObservation m 0)
    (fun k => noisyObservation m (1 / ((k : ℝ) + 1)))
    (measurable_noisyObservation m 0) (fun k => measurable_noisyObservation m _)
    (tendsto_noisyObservation m) _ _ (U := U) (hU := hU)
  intro k V hV
  have hδ : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
  rw [gaussianCoupling_map_noisyObservation ν m _ hδ]
  apply withDensity_apply_le_moment _ _
    (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hp _ _ hV.measurableSet
  have hv : (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1)))) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  simpa only [← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_one, matrixLabelReference]
    using projectionSmoothing_moment hν hsupport
      (gaussianPDF 0 (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
        (sq_nonneg (1 / ((k : ℝ) + 1))))) (measurable_gaussianPDF _ _)
      (lintegral_gaussianPDF_eq_one _ hv) m n hmargin

end ProjectionCoupling

open scoped Pointwise

/-- The Euclidean norm of an ordinary finite coordinate tuple. -/
def coordinateNorm {m : ℕ} (y : Fin m → ℝ) : ℝ := ‖WithLp.toLp 2 y‖

@[fun_prop] lemma continuous_coordinateNorm {m : ℕ} :
    Continuous (coordinateNorm (m := m)) := by
  unfold coordinateNorm
  fun_prop

lemma coordinateNorm_sq {m : ℕ} (y : Fin m → ℝ) :
    coordinateNorm y ^ 2 = ∑ j, (y j)^2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y)

lemma coordinateNorm_smul {m : ℕ} (c : ℝ) (y : Fin m → ℝ) :
    coordinateNorm (c • y) = |c| * coordinateNorm y := by
  simp [coordinateNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

def coordinateBall (m : ℕ) (r : ℝ) : Set (Fin m → ℝ) :=
  {y | coordinateNorm y ≤ r}

lemma measurableSet_coordinateBall (m : ℕ) (r : ℝ) :
    MeasurableSet (coordinateBall m r) :=
  measurableSet_le continuous_coordinateNorm.measurable measurable_const

lemma coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    coordinateBall m (c * r) = c • coordinateBall m r := by
  ext y
  constructor
  · intro hy
    refine ⟨c⁻¹ • y, ?_, by simp [hc.ne']⟩
    change coordinateNorm (c⁻¹ • y) ≤ r
    rw [coordinateNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    exact (inv_mul_le_iff₀ hc).mpr hy
  · rintro ⟨y, hy, rfl⟩
    change coordinateNorm (c • y) ≤ c * r
    rw [coordinateNorm_smul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hy hc.le

lemma volume_coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    volume (coordinateBall m (c * r)) =
      ENNReal.ofReal (c^m) * volume (coordinateBall m r) := by
  rw [coordinateBall_smul m c r hc, Measure.addHaar_smul_of_nonneg volume hc.le]
  simp

lemma gaussianPDF_le_exp (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.exp (-(x^2)/2)) := by
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_left (Real.exp_nonneg _)
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [Real.pi_gt_three]

lemma lintegral_quarterGaussian_le :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(x^2)/4))) ≤ 4 := by
  have he : (fun x : ℝ => Real.exp (-(x^2)/4)) =
      (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  simp_rw [show ∀ x : ℝ, Real.exp (-(x^2)/4) = Real.exp (-(1/4 : ℝ) * x^2) from congrFun he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_sq (by norm_num)) (by filter_upwards [] with x; positivity),
    integral_gaussian]
  have hs : Real.sqrt (Real.pi / (1/4 : ℝ)) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

lemma gaussian_density_pair_bound {m : ℕ} (x y : Fin m → ℝ)
    (h : coordinateNorm y ≤ coordinateNorm x) :
    (∏ j, gaussianPDF 0 1 (x j)) ≤
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
      ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
  calc
    _ ≤ ∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/2)) :=
      Finset.prod_le_prod fun j _ => gaussianPDF_le_exp (x j)
    _ = ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2) / 2)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ ≤ ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2)/4 - (∑ j, (y j)^2)/4)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ coordinateNorm y := norm_nonneg _
      have hs := pow_le_pow_left₀ hn h 2
      rw [coordinateNorm_sq, coordinateNorm_sq] at hs
      linarith
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← Real.exp_sum, ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add]
      congr 2
      simp only [← Finset.sum_div, Finset.sum_neg_distrib]
      ring

lemma measurable_coordinateVolume (m : ℕ) : Measurable (fun x : Fin m → ℝ => volume (coordinateBall m (coordinateNorm x))) := by
  have : Measurable (fun z : (Fin m → ℝ) × (Fin m → ℝ) =>
      ({z | coordinateNorm z.2 ≤ coordinateNorm z.1} : Set _).indicator
        (fun _ => (1 : ℝ≥0∞)) z) :=
    measurable_const.indicator (measurableSet_le (by fun_prop) (by fun_prop))
  change Measurable (Function.uncurry (fun x y : Fin m → ℝ =>
    (coordinateBall m (coordinateNorm x)).indicator (fun _ => (1 : ℝ≥0∞)) y)) at this
  convert this.lintegral_prod_right (ν := (volume : Measure (Fin m → ℝ))) using 1
  ext x
  rw [lintegral_indicator (measurableSet_coordinateBall m _)]
  simp

lemma gaussian_expected_coordinate_volume (m : ℕ) :
    (∫⁻ x : Fin m → ℝ, volume (coordinateBall m (coordinateNorm x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ (16 : ℝ≥0∞)^m := by
  have hB := measurable_coordinateVolume m
  rw [pi_gaussian_withDensity m 1 (by norm_num),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hB]
  have hi (x : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 1 (x j)) * volume (coordinateBall m (coordinateNorm x)) =
      ∫⁻ y : Fin m → ℝ, (coordinateBall m (coordinateNorm x)).indicator
        (fun _ => ∏ j, gaussianPDF 0 1 (x j)) y := by
    rw [lintegral_indicator (measurableSet_coordinateBall m _)]
    simp
  simp only [Pi.mul_apply]
  simp_rw [hi]
  calc
    _ ≤ ∫⁻ x : Fin m → ℝ, ∫⁻ y : Fin m → ℝ,
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
        ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ coordinateBall m (coordinateNorm x)
      · rw [Set.indicator_of_mem hy]
        exact gaussian_density_pair_bound x y hy
      · rw [Set.indicator_of_notMem hy]
        exact zero_le
    _ = ((∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m)^2 := by
      have hJ : (∫⁻ y : Fin m → ℝ, ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))) =
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m := by
        rw [volume_pi, lintegral_fin_prod volume m
          (fun _ => fun z : ℝ => ENNReal.ofReal (Real.exp (-(z^2)/4))) (fun _ => by fun_prop)]
        simp
      have hj (x : Fin m → ℝ) := lintegral_const_mul (μ := volume)
        (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4)))
        (by fun_prop : Measurable (fun y : Fin m → ℝ =>
          ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))))
      simp_rw [hj, hJ]
      rw [lintegral_mul_const _ (by fun_prop), hJ, pow_two]
    _ ≤ ((4 : ℝ≥0∞)^m)^2 := pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ (by positivity) lintegral_quarterGaussian_le m) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_inner_map (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) =
      gaussianReal 0 (NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖)) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  have he : (⇑(innerSL ℝ u)) = (fun x => ⟪u, x⟫) := by
    ext x
    exact innerSL_apply_apply ℝ u x
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  rw [he] at h
  have hh : (‖u‖^2).toNNReal = NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖) := by
    ext
    simp
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hh] using h

lemma rows_inner_map (u : E) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j => ⟪u, A j⟫) =
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun x => ‖u‖ • x) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : E => ⟪u, x⟫)
    (fun _ => (by fun_prop : Measurable (fun x : E => ⟪u, x⟫)).aemeasurable)]
  simp_rw [stdGaussian_inner_map]
  exact (pi_gaussian_map_scale m ‖u‖).symm

lemma rows_expected_coordinate_volume (u : E) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    (∫⁻ A : Fin m → E, volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (16 : ℝ≥0∞)^m := by
  have h := congrArg (fun μ : Measure (Fin m → ℝ) =>
    ∫⁻ y, volume (coordinateBall m (coordinateNorm y)) ∂μ) (rows_inner_map u m)
  rw [lintegral_map (measurable_coordinateVolume m) (by fun_prop),
    lintegral_map (measurable_coordinateVolume m) (by fun_prop)] at h
  rw [h]
  apply le_trans _ (gaussian_expected_coordinate_volume m)
  apply lintegral_mono
  intro x
  apply measure_mono
  intro y hy
  change coordinateNorm y ≤ coordinateNorm x
  apply le_trans hy
  rw [coordinateNorm_smul, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hu

/-- Linear noiseless observation operator, with the Euclidean output norm. -/
def rowOperator {m : ℕ} (A : Fin m → E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowOperator_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowOperator A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  exact real_inner_comm _ _

/-- A measurable common support enclosure indexed by a finite input net. -/
def netProjectionSupport (s : Finset E) (m : ℕ) :
    Set ((Fin m → E) × (Fin m → ℝ)) :=
  ⋃ u ∈ s, {z | coordinateNorm z.2 ≤ 2 * coordinateNorm (fun j => ⟪u, z.1 j⟫)}

lemma measurableSet_netProjectionSupport (s : Finset E) (m : ℕ) :
    MeasurableSet (netProjectionSupport s m) := by
  apply MeasurableSet.biUnion s.countable_toSet
  intro u _
  exact measurableSet_le (by fun_prop) (by fun_prop)

lemma netProjectionSupport_volume (s : Finset E) (hs : ∀ u ∈ s, ‖u‖ ≤ 1) (m : ℕ) :
    matrixLabelReference (E := E) m (netProjectionSupport s m) ≤
      (s.card : ℝ≥0∞) * (32 : ℝ≥0∞)^m := by
  classical
  apply (measure_biUnion_finset_le s _).trans
  calc
    _ ≤ ∑ _u ∈ s, (32 : ℝ≥0∞)^m := by
      apply Finset.sum_le_sum
      intro u hu
      rw [matrixLabelReference, Measure.prod_apply (measurableSet_le (by fun_prop) (by fun_prop))]
      change (∫⁻ A : Fin m → E,
        volume (coordinateBall m (2 * coordinateNorm (fun j => ⟪u, A j⟫)))
        ∂Measure.pi (fun _ => stdGaussian E)) ≤ _
      simp_rw [volume_coordinateBall_smul m 2 _ (by norm_num)]
      have hme : Measurable (fun A : Fin m → E =>
          volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))) :=
        (measurable_coordinateVolume m).comp (by fun_prop)
      rw [lintegral_const_mul _ hme]
      calc
        _ ≤ ENNReal.ofReal ((2 : ℝ)^m) * (16 : ℝ≥0∞)^m :=
          mul_le_mul' le_rfl (rows_expected_coordinate_volume u (hs u hu) m)
        _ = _ := by rw [ENNReal.ofReal_pow (by norm_num)]; norm_num [← mul_pow]
    _ = _ := by simp
end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma opNorm_le_twice_net (f : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/2) :
    ‖f‖ ≤ 2 * (s.sup (fun u => ‖f u‖₊) : ℝ≥0) := by
  classical
  let K : ℝ := (s.sup (fun u => ‖f u‖₊) : ℝ≥0)
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hbound : ‖f‖ ≤ K + ‖f‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx.le
    have hfy : ‖f y‖ ≤ K := by
      exact_mod_cast (Finset.le_sup (f := fun u => ‖f u‖₊) hy)
    calc
      ‖f x‖ = ‖f y + f (x-y)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖f y‖ + ‖f (x-y)‖ := norm_add_le _ _
      _ ≤ K + ‖f‖ * (1/2) := add_le_add hfy
        ((f.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_left
          (by simpa [dist_eq_norm] using hxy) (norm_nonneg _)))
      _ = _ := by ring
  dsimp [K] at hbound
  linarith
end NetNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Common finite-volume enclosure of every noiseless observation from the unit
ball. The constant is exponential in input dimension, uniformly over m ≤ d. -/
theorem exists_projection_support (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∃ D : Set ((Fin m → E) × (Fin m → ℝ)), MeasurableSet D ∧
      (∀ A t, ‖t‖ ≤ 1 → (A, fun j => ⟪t, A j⟫) ∈ D) ∧
      matrixLabelReference (E := E) m D ≤ (192 : ℝ≥0∞)^(Module.finrank ℝ E) := by
  classical
  obtain ⟨s, hs, hc, hnet⟩ := exists_unit_ball_net (E := E)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hsne : s.Nonempty := by
    obtain ⟨u, hu, _⟩ := hnet 0 (by simp)
    exact ⟨u, hu⟩
  refine ⟨netProjectionSupport s m, measurableSet_netProjectionSupport s m, ?_, ?_⟩
  · intro A t ht
    obtain ⟨u, hu, he⟩ := s.exists_mem_eq_sup hsne (fun u => ‖rowOperator A u‖₊)
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ?_⟩⟩
    change coordinateNorm (fun j => ⟪t, A j⟫) ≤
      2 * coordinateNorm (fun j => ⟪u, A j⟫)
    change ‖WithLp.toLp 2 (fun j => ⟪t, A j⟫)‖ ≤
      2 * ‖WithLp.toLp 2 (fun j => ⟪u, A j⟫)‖
    rw [← rowOperator_apply, ← rowOperator_apply]
    calc
      _ ≤ ‖rowOperator A‖ * ‖t‖ := (rowOperator A).le_opNorm t
      _ ≤ ‖rowOperator A‖ := mul_le_of_le_one_right (norm_nonneg _) ht
      _ ≤ _ := by simpa [he] using opNorm_le_twice_net (rowOperator A) s hnet
  · apply (netProjectionSupport_volume s hs m).trans
    have hcard : (s.card : ℝ≥0∞) ≤ (6 : ℝ≥0∞)^(Module.finrank ℝ E) := by
      have h : (s.card : ℝ) ≤ (6 : ℝ)^(Module.finrank ℝ E) := by norm_num at hc ⊢; exact hc
      simpa using ENNReal.ofReal_le_ofReal h
    calc
      _ ≤ (6 : ℝ≥0∞)^Module.finrank ℝ E * (32 : ℝ≥0∞)^Module.finrank ℝ E :=
        mul_le_mul' hcard (pow_le_pow_right₀ (by norm_num) hm)
      _ = _ := by rw [← mul_pow]; norm_num


end SubsphereRegression

end

end OAI
