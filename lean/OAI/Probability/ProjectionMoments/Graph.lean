import OAI.Probability.GaussianRegression.Main
import OAI.Probability.ProjectionMoments.Model

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

lemma volume_preserving_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry ι κ ℝ).symm
  refine ⟨(MeasurableEquiv.curry ι κ ℝ).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry ι κ ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i,j))) := by
    ext x
    simp [Set.mem_pi, MeasurableEquiv.curry, Function.uncurry]
  rw [he, volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => (volume : Measure ℝ) (s p))).symm

lemma volume_preserving_transpose (m n : ℕ) :
    MeasurePreserving (fun A : Fin m → Fin n → ℝ => fun i j => A j i) := by
  have h1 := (volume_preserving_curry (Fin m) (Fin n)).symm
  have h2 := volume_measurePreserving_piCongrLeft
    (fun _ : Fin n × Fin m => ℝ) (Equiv.prodComm (Fin m) (Fin n))
  have h3 := volume_preserving_curry (Fin n) (Fin m)
  exact h3.comp (h2.comp h1)

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_graph_kernel_bound {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (m : ℕ)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) (b : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, ∏ i, φ (fun j => b j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun Z => ∏ i, φ (fun j => b j - Z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  change (∫⁻ A : Fin m → E, H (fun j i => ⟪v i, A j⟫)
    ∂Measure.pi (fun _ => stdGaussian E)) ≤ _
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ Z, H Z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (NoiselessRegression.gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) := by
      rw [lintegral_smul_measure]
      have hL : ∫⁻ Z, H Z = 1 := by
        have h := (volume_preserving_transpose m n).lintegral_comp
          (show Measurable (fun Z : Fin n → Fin m → ℝ => ∏ i, φ (b - Z i)) by fun_prop)
        change (∫⁻ Z : Fin m → Fin n → ℝ, ∏ i, φ (b - fun j => Z j i)) = _ at h
        rw [show (∫⁻ Z, H Z) = ∫⁻ Z : Fin n → Fin m → ℝ, ∏ i, φ (b - Z i) from h]
        rw [volume_pi, NoiselessRegression.lintegral_fin_prod volume n
          (fun _ y => φ (b - y)) (by intro i; fun_prop)]
        simp_rw [lintegral_sub_left_eq_self φ b, hφ1]
        simp
      simp [hL, smul_eq_mul]

lemma measurable_vectorSmoothing (ν : Measure E) [SFinite ν] (m : ℕ)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (vectorSmoothing ν m φ) := by
  apply Measurable.lintegral_prod_right
  exact hφ.comp (by fun_prop)

theorem vectorSmoothing_graph_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) (z : E) (b : Fin m → ℝ) :
    ∫⁻ A : Fin m → E,
      (vectorSmoothing ν m φ (A, fun j => ⟪z, A j⟫ + b j)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (NoiselessRegression.replicaConstant ν a m) ^ q := by
  have he (A : Fin m → E) (t : E) :
      (fun j => (⟪z, A j⟫ + b j) - ⟪t, A j⟫) =
        (fun j => b j - ⟪t-z, A j⟫) := by
    funext j
    rw [inner_sub_left]
    ring
  simp only [vectorSmoothing, he]
  have hp (A : Fin m → E) := NoiselessRegression.lintegral_pow_pi ν
    (fun t => φ (fun j => b j - ⟪t-z, A j⟫)) (by fun_prop) q
  simp_rw [hp]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ v : Fin q → E, NoiselessRegression.replicaWeight m z v
        ∂Measure.pi (fun _ => ν) := by
      apply lintegral_mono_ae
      filter_upwards [NoiselessRegression.ae_replica_linearIndependent hν hsupport z q
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [NoiselessRegression.replicaWeight_eq_det, NoiselessRegression.sqrt_det_gram]
      exact gaussian_graph_kernel_bound (fun i => v i - z) hv m φ hφ hφ1 b
    _ ≤ _ := NoiselessRegression.replica_integral_bound hν hsupport m z q hmargin
end GaussianGraph

lemma measurable_ballKernel (m : ℕ) (η : ℝ) : Measurable (ballKernel m η) := by
  exact (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable

lemma ballKernel_integral (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ y, ballKernel m η y = 1 := by
  have hm : Measurable ((Metric.closedBall (0 : Label m) η).indicator
      (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹)) :=
    measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  change (∫⁻ y, (Metric.closedBall (0 : Label m) η).indicator
    (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹) (WithLp.toLp 2 y)) = 1
  rw [(PiLp.volume_preserving_toLp (Fin m)).lintegral_comp hm,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  apply ENNReal.inv_mul_cancel
  · exact ne_of_gt ((Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr hη)).trans_le (measure_mono Metric.ball_subset_closedBall))
  · exact (isCompact_closedBall (0 : Label m) η).measure_lt_top.ne

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma rowMap_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowMap A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  simp [rowMap, real_inner_comm]

lemma measurable_ballAverage (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ) :
    Measurable (ballAverage ν m η) := by
  exact (measurable_vectorSmoothing ν m (ballKernel m η)
    (measurable_ballKernel m η)).comp
      (measurable_fst.prodMk ((PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).measurable.comp
        measurable_snd))

omit [FiniteDimensional ℝ E] in
lemma ballAverage_eq (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage ν m η (A,y) =
      (ν.map (rowMap A)) (Metric.closedBall y η) /
        volume (Metric.closedBall y η) := by
  have he (t : E) :
      (fun j => WithLp.ofLp y j - ⟪t, A j⟫) = WithLp.ofLp (y - rowMap A t) := by
    simp only [rowMap_apply, WithLp.ofLp_sub]
    rfl
  have hpoint (t : E) :
      ballKernel m η (fun j => WithLp.ofLp y j - ⟪t, A j⟫) =
        (Metric.closedBall y η).indicator
          (fun _ => (volume (Metric.closedBall y η))⁻¹) (rowMap A t) := by
    rw [ballKernel, he, WithLp.toLp_ofLp, Measure.addHaar_closedBall_center volume y]
    have hh : y - rowMap A t ∈ Metric.closedBall (0 : Label m) η ↔
        rowMap A t ∈ Metric.closedBall y η := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    by_cases h : rowMap A t ∈ Metric.closedBall y η
    · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hh.mpr h)]
    · simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (not_congr hh |>.mpr h)]
  simp only [ballAverage, vectorSmoothing, hpoint]
  rw [← lintegral_map (measurable_const.indicator Metric.isClosed_closedBall.measurableSet)
    (rowMap A).continuous.measurable,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp [div_eq_mul_inv, mul_comm]

lemma measurable_lowerDensity (ν : Measure E) [SFinite ν] (m : ℕ) :
    Measurable (lowerDensity ν m) :=
  Measurable.liminf (fun _n => measurable_ballAverage ν m _)

lemma ballAverage_graph_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a)
    (z : E) (b : Label m) {η : ℝ} (hη : 0 < η) :
    ∫⁻ A : Fin m → E, (ballAverage ν m η (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (NoiselessRegression.replicaConstant ν a m) ^ q := by
  simpa only [ballAverage, rowMap_apply, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_def] using
    vectorSmoothing_graph_moment hν hsupport m q hmargin (ballKernel m η)
      (measurable_ballKernel m η) (ballKernel_integral m hη) z (WithLp.ofLp b)

theorem lowerDensity_graph_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a) (z : E) (b : Label m) :
    ∫⁻ A : Fin m → E, (lowerDensity ν m (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (NoiselessRegression.replicaConstant ν a m) ^ q := by
  have hp (u : ℕ → ℝ≥0∞) : (liminf u atTop) ^ q = liminf (fun n => u n ^ q) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x ^ q) from (fun _ _ h => pow_le_pow_left' h q)).map_liminf_of_continuousAt
      u (ENNReal.continuous_pow q).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun n => ?_)).trans
  · apply liminf_le_of_frequently_le'
    exact Filter.Frequently.of_forall (fun n => ballAverage_graph_moment hν hsupport m q hmargin z b
      (inv_pos.mpr (by positivity)))
  · apply Measurable.pow_const
    apply (measurable_ballAverage ν m _).comp
    exact measurable_id.prodMk (by simp only [rowMap_apply]; fun_prop)

theorem lowerDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (rowMap A) ≪ (volume : Measure (Label m))) :
    volume.withDensity (fun y => lowerDensity ν m (A,y)) = ν.map (rowMap A) := by
  let ρ := ν.map (rowMap A)
  let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Label m)) 1
  have hneg : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · change (0 : ℝ) < ((n : ℝ) + 1)⁻¹
      positivity
  have hae : (fun y => lowerDensity ν m (A,y)) =ᵐ[volume] ρ.rnDeriv volume := by
    filter_upwards [v.ae_tendsto_rnDeriv_of_absolutelyContinuous hA] with y hy
    have ht := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
      (K := (1 : ℝ)) (x := y) (fun _ : ℕ => y) (fun n => ((n : ℝ) + 1)⁻¹) hneg
      (Filter.Eventually.of_forall (fun n => Metric.mem_closedBall_self (by positivity)))
    have hlim := (hy.comp ht).liminf_eq
    simpa only [lowerDensity, ballAverage_eq, ρ, Function.comp_def] using hlim
  rw [withDensity_congr_ae hae]
  exact Measure.withDensity_rnDeriv_eq _ _ hA

lemma ballAverage_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R η : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R + η < ‖y - rowMap A z‖) :
    ballAverage ν m η (A,y) = 0 := by
  have hz : (ν.map (rowMap A)) (Metric.closedBall y η) = 0 := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ν.support_mem_ae] with t ht hty
    have htR : ‖t-z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupport ht
    have hty' : ‖y - rowMap A t‖ ≤ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hty
    have hn : ‖rowMap A t - rowMap A z‖ ≤ ‖rowMap A‖ * R := by
      rw [← map_sub]
      exact ((rowMap A).le_opNorm _).trans (mul_le_mul_of_nonneg_left htR (norm_nonneg _))
    have hb : ‖y - rowMap A z‖ ≤ η + ‖rowMap A‖ * R := by
      calc
        _ = ‖(y - rowMap A t) + (rowMap A t - rowMap A z)‖ := by congr 1; abel
        _ ≤ ‖y - rowMap A t‖ + ‖rowMap A t - rowMap A z‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hty' hn
    linarith
  simp only [ballAverage_eq, hz, ENNReal.zero_div]

theorem lowerDensity_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R < ‖y - rowMap A z‖) :
    lowerDensity ν m (A,y) = 0 := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : ∀ᶠ n : ℕ in atTop, ballAverage ν m ((n : ℝ) + 1)⁻¹ (A,y) = 0 := by
    filter_upwards [ht (Iio_mem_nhds (sub_pos.mpr hfar))] with n hn
    apply ballAverage_eq_zero_of_far ν m A z R _ y hsupport
    have hnn : ((n : ℝ) + 1)⁻¹ < ‖y - rowMap A z‖ - ‖rowMap A‖ * R := hn
    linarith
  exact (liminf_congr he).trans (liminf_const _)
end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rescale (z : E) (R : ℝ) (x : E) : E := R⁻¹ • (x-z)
def dilate (z : E) (R : ℝ) (x : E) : E := R • x + z

omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_rescale (z : E) (R : ℝ) : Measurable (rescale z R) := by
  unfold rescale; fun_prop
omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_dilate (z : E) (R : ℝ) : Measurable (dilate z R) := by
  unfold dilate; fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dilate_rescale (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    dilate z R (rescale z R x) = x := by
  simp [dilate, rescale, smul_smul, hR]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rescale_preimage_closedBall (z b : E) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    rescale z R ⁻¹' Metric.closedBall b t = Metric.closedBall (dilate z R b) (R*t) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have he : rescale z R x - b = R⁻¹ • (x - dilate z R b) := by
    simp [rescale, dilate, smul_sub, smul_add, smul_smul, hR.ne', sub_sub, add_comm]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [inv_mul_le_iff₀ hR]

def normalizedRescale (ν : Measure E) (K a : ℝ) (z : E) (R : ℝ) : Measure E :=
  (ENNReal.ofReal (K * R ^ a))⁻¹ • ν.map (rescale z R)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma normalizedRescale_finite (ν : Measure E) [IsFiniteMeasure ν]
    (K a : ℝ) (z : E) (R : ℝ) (hKR : 0 < K * R ^ a) :
    IsFiniteMeasure (normalizedRescale ν K a z R) := by
  dsimp [normalizedRescale]
  exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hKR))

omit [FiniteDimensional ℝ E] in
lemma normalizedRescale_local {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R) :
    NoiselessRegression.HasLocalMassBound (normalizedRescale ν K a z R) a := by
  intro b _ t ht
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall z b hR]
  apply (mul_le_mul' le_rfl (hν (dilate z R b) (R*t) (mul_pos hR ht))).trans
  rw [Real.mul_rpow hR.le ht.le, ← mul_assoc,
    ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hR.le a)),
    ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
      ENNReal.ofReal_ne_top, one_mul]

lemma normalizedRescale_support {ν : Measure E} (K a : ℝ) (z : E) {R : ℝ}
    (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R) :
    (normalizedRescale ν K a z R).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  apply Measure.smul_absolutelyContinuous.ae_le
  change ∀ᵐ x ∂ν.map (rescale z R), x ∈ Metric.closedBall 0 1
  apply (ae_map_iff (measurable_rescale z R).aemeasurable
    (show MeasurableSet {x : E | x ∈ Metric.closedBall 0 1} from
      Metric.isClosed_closedBall.measurableSet)).mpr
  filter_upwards [ν.support_mem_ae] with x hx
  have he := rescale_preimage_closedBall z (0 : E) hR (1 : ℝ)
  have hx' : x ∈ rescale z R ⁻¹' Metric.closedBall 0 1 := by
    rw [he]
    simpa [dilate] using hsupport hx
  exact hx'

omit [FiniteDimensional ℝ E] in
lemma normalizedRescale_recover (ν : Measure E) (K a : ℝ) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (K * R ^ a) • (normalizedRescale ν K a z R).map (dilate z R) = ν := by
  rw [normalizedRescale, Measure.map_smul _ (measurable_dilate z R).aemeasurable, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top,
    one_smul, Measure.map_map (measurable_dilate z R) (measurable_rescale z R)]
  have he : dilate z R ∘ rescale z R = id := by
    funext x; exact dilate_rescale z hR.ne' x
  rw [he, Measure.map_id]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma ballAverage_smul (ν : Measure E) (c : ℝ≥0∞) (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage (c • ν) m η (A,y) = c * ballAverage ν m η (A,y) := by
  simp only [ballAverage, vectorSmoothing, lintegral_smul_measure, smul_eq_mul]

lemma ballAverage_dilate (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (A : Fin m → E) (b : Label m) :
    ballAverage (ν.map (dilate z R)) m η (A, rowMap A z + b) =
      (ENNReal.ofReal (R ^ m))⁻¹ * ballAverage ν m (η/R) (A, R⁻¹ • b) := by
  rw [ballAverage_eq, ballAverage_eq]
  have hn : ((ν.map (dilate z R)).map (rowMap A)) (Metric.closedBall (rowMap A z + b) η) =
      (ν.map (rowMap A)) (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet,
      Measure.map_apply (measurable_dilate z R)
        (Metric.isClosed_closedBall.measurableSet.preimage (rowMap A).continuous.measurable),
      Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    have he : rowMap A (dilate z R x) - (rowMap A z + b) =
        R • (rowMap A x - R⁻¹ • b) := by
      simp only [dilate, map_add, map_smul, smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hR, le_div_iff₀ hR, mul_comm]
  have hv : volume (Metric.closedBall (rowMap A z + b) η) =
      ENNReal.ofReal (R ^ m) * volume (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.addHaar_closedBall volume _ hη.le,
      Measure.addHaar_closedBall volume _ (div_pos hη hR).le,
      finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow, mul_div_cancel₀ _ hR.ne']
  rw [hn, hv, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))) (Or.inl ENNReal.ofReal_ne_top)]
  rw [ENNReal.div_eq_inv_mul, mul_assoc]

lemma normalizedRescale_mass {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R)
    (hsupport : ν.support ⊆ Metric.closedBall z R) :
    normalizedRescale ν K a z R Set.univ ≤ 1 := by
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    apply propext
    exact iff_of_true (Set.mem_univ x) (hsupport hx)
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) MeasurableSet.univ, Set.preimage_univ, he]
  exact (mul_le_mul' le_rfl (hν z R hR)).trans_eq
    (ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top)

lemma ballAverage_normalizedRescale {ν : Measure E} [IsFiniteMeasure ν]
    (K a : ℝ) (hK : 0 < K) (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (m : ℕ) (A : Fin m → E) (b : Label m) :
    ballAverage ν m η (A, rowMap A z + b) =
      ENNReal.ofReal (K * R ^ (a-m)) *
        ballAverage (normalizedRescale ν K a z R) m (η/R) (A, R⁻¹ • b) := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  conv_lhs => rw [← normalizedRescale_recover ν K a hK z hR]
  rw [ballAverage_smul, ballAverage_dilate μ m z hR hη, ← mul_assoc]
  congr 1
  rw [Real.rpow_sub_natCast hR.ne', ← mul_div_assoc, ENNReal.ofReal_div_of_pos (by positivity)]
  rfl

theorem ballAverage_graph_moment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a) (b : Label m) {η : ℝ} (hη : 0 < η) :
    ∫⁻ A : Fin m → E, (ballAverage ν m η (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (ENNReal.ofReal (K * R ^ (a-m)) *
        (1 + ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * (4 : ℝ)^a) *
          (2 : ℝ≥0∞)^(m+1))) ^ q := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  have hl := normalizedRescale_local hν hK z hR
  have hs := normalizedRescale_support K a z hR hsupport
  have hc : NoiselessRegression.replicaConstant μ a m ≤
      1 + ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * (4 : ℝ)^a) * (2 : ℝ≥0∞)^(m+1) := by
    exact add_le_add (normalizedRescale_mass hν hK z hR hsupport) le_rfl
  simp_rw [ballAverage_normalizedRescale K a hK z hR hη, mul_pow]
  rw [lintegral_const_mul _ (by apply Measurable.pow_const; exact
    (measurable_ballAverage μ m (η/R)).comp (measurable_id.prodMk measurable_const))]
  apply mul_le_mul' le_rfl
  have hm := ballAverage_graph_moment hl hs m q hmargin (0 : E)
    (R⁻¹ • b) (div_pos hη hR)
  have hz (A : Fin m → E) : rowMap A (0 : E) = 0 := map_zero (rowMap A)
  simp only [hz, zero_add] at hm
  exact hm.trans (pow_le_pow_left' hc q)

theorem lowerDensity_graph_moment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a) (b : Label m) :
    ∫⁻ A : Fin m → E, (lowerDensity ν m (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (ENNReal.ofReal (K * R ^ (a-m)) *
        (1 + ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * (4 : ℝ)^a) *
          (2 : ℝ≥0∞)^(m+1))) ^ q := by
  have hp (u : ℕ → ℝ≥0∞) : (liminf u atTop) ^ q = liminf (fun n => u n ^ q) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x ^ q) from (fun _ _ h => pow_le_pow_left' h q)).map_liminf_of_continuousAt
      u (ENNReal.continuous_pow q).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun n => ?_)).trans
  · apply liminf_le_of_frequently_le'
    exact Filter.Frequently.of_forall (fun n => ballAverage_graph_moment_scaled hν hK z hR
      hsupport m q hmargin b (inv_pos.mpr (by positivity)))
  · apply Measurable.pow_const
    apply (measurable_ballAverage ν m _).comp
    exact measurable_id.prodMk (by simp only [rowMap_apply]; fun_prop)

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_vector_replica_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (m : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      φ (fun j => y j - ⟪p, A j⟫) *
        ∏ i, φ (fun j => y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i-p) i‖)⁻¹ ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, φ (fun j => y j - ⟪p, A j⟫) *
        ∏ i, φ (fun j => y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, φ y * ∏ i, φ (fun j => y j - ⟪v i-p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) :
        (fun j => y j - ⟪p, A j⟫ - ⟪v i-p, A j⟫) =
        (fun j => y j - ⟪v i, A j⟫) := by
      funext j; rw [inner_sub_left]; ring
    convert (lintegral_sub_right_eq_self (μ := (volume : Measure (Fin m → ℝ)))
        (fun y : Fin m → ℝ => φ y * ∏ i, φ (fun j => y j - ⟪v i-p, A j⟫))
        (fun j => ⟪p, A j⟫)) using 1
    apply lintegral_congr
    intro y
    simp only [Pi.sub_apply, he]
    rfl
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y, φ y * ENNReal.ofReal
        ((∏ i, ‖gramSchmidt ℝ (fun i => v i-p) i‖)⁻¹ ^ m) := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [lintegral_const_mul _ (by fun_prop)]
      exact mul_le_mul' le_rfl (gaussian_graph_kernel_bound _ hv m φ hφ hφ1 y)
    _ = _ := by rw [lintegral_mul_const _ hφ, hφ1, one_mul]

lemma vectorSmoothing_pow (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (vectorSmoothing ν m φ z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        φ (fun j => z.2 j - ⟪w.1, z.1 j⟫) *
          ∏ i, φ (fun j => z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, φ (fun j => z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← NoiselessRegression.lintegral_pow_pi ν
    (fun t : E => φ (fun j => z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

theorem vectorSmoothing_integrated_moment {m : ℕ} {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ y, φ y = 1)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ), (vectorSmoothing ν m φ z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  simp_rw [vectorSmoothing_pow ν m n φ hφ]
  rw [lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ v : Fin n → E, NoiselessRegression.replicaWeight m p v
        ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [NoiselessRegression.ae_replica_linearIndependent hν hsupport p n
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [lintegral_prod _ (by fun_prop), NoiselessRegression.replicaWeight_eq_det,
        NoiselessRegression.sqrt_det_gram]
      exact gaussian_vector_replica_bound p v hv m φ hφ hφ1
    _ ≤ ∫⁻ _p, (NoiselessRegression.replicaConstant ν a m)^n ∂ν :=
      lintegral_mono fun p => NoiselessRegression.replica_integral_bound hν hsupport m p n hmargin
    _ = _ := by rw [lintegral_const, mul_comm]

theorem ballAverage_integrated_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) {η : ℝ} (hη : 0 < η) :
    ∫⁻ z : (Fin m → E) × Label m, (ballAverage ν m η z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  have hm := (MeasurePreserving.id (Measure.pi (fun _ : Fin m => stdGaussian E))).prod
    (PiLp.volume_preserving_toLp (Fin m))
  rw [← hm.lintegral_comp ((measurable_ballAverage ν m η).pow_const (n+1))]
  exact vectorSmoothing_integrated_moment hν hsupport _ (measurable_ballKernel m η)
    (ballKernel_integral m hη) n hmargin

theorem lowerDensity_integrated_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × Label m, (lowerDensity ν m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  have hp (u : ℕ → ℝ≥0∞) : (liminf u atTop) ^ (n+1) =
      liminf (fun j => u j ^ (n+1)) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x ^ (n+1)) from
      (fun _ _ h => pow_le_pow_left' h (n+1))).map_liminf_of_continuousAt
      u (ENNReal.continuous_pow (n+1)).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun j => (measurable_ballAverage ν m _).pow_const _)).trans
  apply liminf_le_of_frequently_le'
  exact Filter.Frequently.of_forall (fun j => ballAverage_integrated_moment hν hsupport m n
    hmargin (inv_pos.mpr (by positivity)))

end ProjectionMoments
end

end OAI
