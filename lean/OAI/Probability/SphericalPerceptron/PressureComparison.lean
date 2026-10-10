import Mathlib

namespace OAI

/-!
# Spherical pressure comparisons for invariant operator disorder

The pressure convergence theorem assumes convergence in probability. The Gaussian cavity/contact
and global penalty limits, angular limit identification, finite radial Laplace formula, spectral
mesh convergence, and unconditional pressure convergence under the spectral hypotheses remain
unproved. The variational functionals and limit predicates below define quantities and statements,
not proofs of these limits.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace SphericalPerceptron.InvariantDisorder

universe u
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Disorder (M N : ℕ) := Vec N →L[ℝ] Vec M

def spherePoint (N : ℕ) (x : Vec N) : Vec N :=
  (Real.sqrt N / ‖x‖) • x

lemma measurable_spherePoint (N : ℕ) : Measurable (spherePoint N) := by
  unfold spherePoint
  fun_prop

def sphereMeasure (N : ℕ) : Measure (Vec N) :=
  (stdGaussian (Vec N)).map (spherePoint N)

instance (N : ℕ) : IsProbabilityMeasure (sphereMeasure N) := by
  unfold sphereMeasure
  infer_instance

def rowEnergy {M N : ℕ} (A : Disorder M N) (f : ℝ →ᵇ ℝ) (x : Vec N) : ℝ :=
  ∑ r : Fin M, f (A x r)

def pressure {M N : ℕ} (A : Disorder M N) (f : ℝ →ᵇ ℝ) : ℝ :=
  (N : ℝ)⁻¹ * Real.log (∫ x, Real.exp (rowEnergy A f x) ∂sphereMeasure N)

lemma continuous_rowEnergy {M N : ℕ} (A : Disorder M N) (f : ℝ →ᵇ ℝ) :
    Continuous (rowEnergy A f) := by
  unfold rowEnergy
  fun_prop

lemma rowEnergy_abs_le {M N : ℕ} (A : Disorder M N) (f : ℝ →ᵇ ℝ) (x : Vec N) :
    |rowEnergy A f x| ≤ (M : ℝ) * ‖f‖ := by
  calc
    |rowEnergy A f x| = ‖∑ r : Fin M, f (A x r)‖ := by simp [rowEnergy]
    _ ≤ ∑ r : Fin M, ‖f (A x r)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin M, ‖f‖ := Finset.sum_le_sum fun r _ => f.norm_coe_le_norm _
    _ = (M : ℝ) * ‖f‖ := by simp

section BoundedLogPartition
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma integrable_exp_of_abs_le (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, |u x| ≤ C) : Integrable (fun x => Real.exp (u x)) μ := by
  refine (integrable_const (Real.exp C)).mono' (Real.continuous_exp.comp_aestronglyMeasurable hu) ?_
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    Real.exp_le_exp.mpr (abs_le.mp hx).2

lemma exp_integral_bounds (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, |u x| ≤ C) :
    Real.exp (-C) ≤ ∫ x, Real.exp (u x) ∂μ ∧
      (∫ x, Real.exp (u x) ∂μ) ≤ Real.exp C := by
  have hi := integrable_exp_of_abs_le u hu C hb
  constructor
  · calc
      Real.exp (-C) = ∫ _, Real.exp (-C) ∂μ := by simp
      _ ≤ ∫ x, Real.exp (u x) ∂μ := integral_mono_ae (integrable_const _) hi <| by
        filter_upwards [hb] with x hx
        exact Real.exp_le_exp.mpr (abs_le.mp hx).1
  · calc
      (∫ x, Real.exp (u x) ∂μ) ≤ ∫ _, Real.exp C ∂μ :=
        integral_mono_ae hi (integrable_const _) <| by
          filter_upwards [hb] with x hx
          exact Real.exp_le_exp.mpr (abs_le.mp hx).2
      _ = Real.exp C := by simp

lemma log_integral_exp_abs_le (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, |u x| ≤ C) :
    |Real.log (∫ x, Real.exp (u x) ∂μ)| ≤ C := by
  obtain ⟨hlo, hhi⟩ := exp_integral_bounds u hu C hb
  have hpos := (Real.exp_pos (-C)).trans_le hlo
  rw [abs_le]
  constructor
  · simpa using Real.log_le_log (Real.exp_pos (-C)) hlo
  · simpa using Real.log_le_log hpos hhi

lemma log_integral_exp_le_add (u v : X → ℝ)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (C D : ℝ) (hub : ∀ᵐ x ∂μ, |u x| ≤ C) (hvb : ∀ᵐ x ∂μ, |v x| ≤ C)
    (huv : ∀ᵐ x ∂μ, u x ≤ D + v x) :
    Real.log (∫ x, Real.exp (u x) ∂μ) ≤ D + Real.log (∫ x, Real.exp (v x) ∂μ) := by
  have hiu := integrable_exp_of_abs_le u hu C hub
  have hiv := integrable_exp_of_abs_le v hv C hvb
  have hpu := (Real.exp_pos (-C)).trans_le (exp_integral_bounds u hu C hub).1
  have hpv := (Real.exp_pos (-C)).trans_le (exp_integral_bounds v hv C hvb).1
  have hcmp : (∫ x, Real.exp (u x) ∂μ) ≤ Real.exp D * ∫ x, Real.exp (v x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hiu (hiv.const_mul _)
    filter_upwards [huv] with x hx
    simpa only [Real.exp_add] using Real.exp_le_exp.mpr hx
  calc
    Real.log (∫ x, Real.exp (u x) ∂μ) ≤
        Real.log (Real.exp D * ∫ x, Real.exp (v x) ∂μ) := Real.log_le_log hpu hcmp
    _ = D + Real.log (∫ x, Real.exp (v x) ∂μ) := by
      rw [Real.log_mul (Real.exp_ne_zero _) hpv.ne', Real.log_exp]

lemma log_integral_exp_sub_abs_le (u v : X → ℝ)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (C D : ℝ) (hub : ∀ᵐ x ∂μ, |u x| ≤ C) (hvb : ∀ᵐ x ∂μ, |v x| ≤ C)
    (huv : ∀ᵐ x ∂μ, |u x - v x| ≤ D) :
    |Real.log (∫ x, Real.exp (u x) ∂μ) - Real.log (∫ x, Real.exp (v x) ∂μ)| ≤ D := by
  have h₁ := log_integral_exp_le_add u v hu hv C D hub hvb (by
    filter_upwards [huv] with x hx
    have h := (abs_le.mp hx).2
    linarith)
  have h₂ := log_integral_exp_le_add v u hv hu C D hvb hub (by
    filter_upwards [huv] with x hx
    have h := (abs_le.mp hx).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end BoundedLogPartition

lemma pressure_abs_le {M N : ℕ} (A : Disorder M N) (f : ℝ →ᵇ ℝ) :
    |pressure A f| ≤ (M : ℝ) / N * ‖f‖ := by
  have h := log_integral_exp_abs_le (μ := sphereMeasure N) (rowEnergy A f)
    (continuous_rowEnergy A f).aestronglyMeasurable ((M : ℝ) * ‖f‖)
    (Filter.Eventually.of_forall (rowEnergy_abs_le A f))
  calc
    |pressure A f| = (N : ℝ)⁻¹ * |Real.log (∫ x, Real.exp (rowEnergy A f x) ∂sphereMeasure N)| := by
      rw [pressure, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
    _ ≤ (N : ℝ)⁻¹ * ((M : ℝ) * ‖f‖) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = (M : ℝ) / N * ‖f‖ := by ring

lemma continuous_pressure {M N : ℕ} (f : ℝ →ᵇ ℝ) :
    Continuous (fun A : Disorder M N => pressure A f) := by
  have hc : Continuous (fun A : Disorder M N =>
      ∫ x, Real.exp (rowEnergy A f x) ∂sphereMeasure N) := by
    apply continuous_of_dominated (bound := fun _ => Real.exp ((M : ℝ) * ‖f‖))
    · intro A
      exact (continuous_rowEnergy A f).rexp.aestronglyMeasurable
    · intro A
      filter_upwards with x
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        Real.exp_le_exp.mpr (abs_le.mp (rowEnergy_abs_le A f x)).2
    · exact integrable_const _
    · filter_upwards with x
      unfold rowEnergy
      fun_prop
  apply continuous_const.mul (hc.log ?_)
  intro A
  exact ne_of_gt ((Real.exp_pos (-((M : ℝ) * ‖f‖))).trans_le
    (exp_integral_bounds (rowEnergy A f) (continuous_rowEnergy A f).aestronglyMeasurable
      ((M : ℝ) * ‖f‖) (Filter.Eventually.of_forall (rowEnergy_abs_le A f))).1)

lemma spherePoint_norm_le (N : ℕ) (x : Vec N) : ‖spherePoint N x‖ ≤ Real.sqrt N := by
  by_cases hx : x = 0
  · simp [spherePoint, hx, Real.sqrt_nonneg]
  · rw [spherePoint, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

lemma sphereMeasure_norm_le (N : ℕ) :
    ∀ᵐ x ∂sphereMeasure N, ‖x‖ ≤ Real.sqrt N := by
  rw [sphereMeasure, ae_map_iff (measurable_spherePoint N).aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  exact Filter.Eventually.of_forall (spherePoint_norm_le N)

lemma sphereMeasure_map (N : ℕ) (U : Vec N ≃ₗᵢ[ℝ] Vec N) :
    (sphereMeasure N).map U = sphereMeasure N := by
  have hcomm : (U ∘ spherePoint N) = (spherePoint N ∘ U) := by
    ext x
    simp [spherePoint]
  rw [sphereMeasure, Measure.map_map U.continuous.measurable (measurable_spherePoint N),
    hcomm, ← Measure.map_map (measurable_spherePoint N) U.continuous.measurable,
    stdGaussian_map]

lemma stdGaussian_vec_zero (N : ℕ) (hN : 0 < N) :
    (stdGaussian (Vec N)) {0} = 0 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_apply (WithLp.measurable_toLp 2 (Fin N → ℝ)) (measurableSet_singleton _)]
  have hpre : (WithLp.toLp 2 : (Fin N → ℝ) → Vec N) ⁻¹' {0} = {0} := by
    ext x
    simp
  rw [hpre, measure_singleton]

lemma sphereMeasure_norm_sq (N : ℕ) :
    ∀ᵐ x ∂sphereMeasure N, ‖x‖ ^ 2 = (N : ℝ) := by
  rw [sphereMeasure, ae_map_iff (measurable_spherePoint N).aemeasurable
    (measurableSet_eq_fun (measurable_norm.pow_const _) measurable_const)]
  by_cases hN : N = 0
  · subst N
    filter_upwards with x
    simp [spherePoint]
  · have hzero : ∀ᵐ x ∂stdGaussian (Vec N), x ≠ 0 := by
      rw [ae_iff]
      simpa using stdGaussian_vec_zero N (Nat.pos_of_ne_zero hN)
    filter_upwards [hzero] with x hx
    rw [spherePoint, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx), Real.sq_sqrt (Nat.cast_nonneg N)]

lemma sum_abs_le_sqrt_mul_norm {M : ℕ} (y : Vec M) :
    (∑ r : Fin M, |y r|) ≤ Real.sqrt M * ‖y‖ := by
  simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin M => (1 : ℝ)) (fun r => |y r|)

lemma rowEnergy_sub_abs_le {M N : ℕ} (A B : Disorder M N) (f : ℝ →ᵇ ℝ)
    {K : NNReal} (hf : LipschitzWith K f) (x : Vec N) :
    |rowEnergy A f x - rowEnergy B f x| ≤
      (K : ℝ) * (Real.sqrt M * (‖A - B‖ * ‖x‖)) := by
  calc
    |rowEnergy A f x - rowEnergy B f x| =
        ‖∑ r : Fin M, (f (A x r) - f (B x r))‖ := by
      simp [rowEnergy, Finset.sum_sub_distrib]
    _ ≤ ∑ r : Fin M, ‖f (A x r) - f (B x r)‖ := norm_sum_le _ _
    _ ≤ ∑ r : Fin M, (K : ℝ) * |((A - B) x) r| := by
      apply Finset.sum_le_sum
      intro r _
      change ‖f (A x r) - f (B x r)‖ ≤ (K : ℝ) * |A x r - B x r|
      simpa only [Real.norm_eq_abs] using hf.norm_sub_le (A x r) (B x r)
    _ = (K : ℝ) * ∑ r : Fin M, |((A - B) x) r| := by rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (Real.sqrt M * ‖(A - B) x‖) :=
      mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_mul_norm _) K.coe_nonneg
    _ ≤ (K : ℝ) * (Real.sqrt M * (‖A - B‖ * ‖x‖)) := by
      gcongr
      exact (A - B).le_opNorm x

theorem pressure_operator_stability {M N : ℕ} (A B : Disorder M N) (f : ℝ →ᵇ ℝ)
    {K : NNReal} (hf : LipschitzWith K f) :
    |pressure A f - pressure B f| ≤ (K : ℝ) * Real.sqrt ((M : ℝ) / N) * ‖A - B‖ := by
  have hd := log_integral_exp_sub_abs_le (μ := sphereMeasure N)
    (rowEnergy A f) (rowEnergy B f)
    (continuous_rowEnergy A f).aestronglyMeasurable
    (continuous_rowEnergy B f).aestronglyMeasurable
    ((M : ℝ) * ‖f‖) ((K : ℝ) * (Real.sqrt M * (‖A - B‖ * Real.sqrt N)))
    (Filter.Eventually.of_forall (rowEnergy_abs_le A f))
    (Filter.Eventually.of_forall (rowEnergy_abs_le B f)) (by
      filter_upwards [sphereMeasure_norm_le N] with x hx
      exact (rowEnergy_sub_abs_le A B f hf x).trans (by gcongr))
  calc
    |pressure A f - pressure B f| = (N : ℝ)⁻¹ *
        |Real.log (∫ x, Real.exp (rowEnergy A f x) ∂sphereMeasure N) -
          Real.log (∫ x, Real.exp (rowEnergy B f x) ∂sphereMeasure N)| := by
      rw [pressure, pressure, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
    _ ≤ (N : ℝ)⁻¹ * ((K : ℝ) * (Real.sqrt M * (‖A - B‖ * Real.sqrt N))) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (K : ℝ) * Real.sqrt M * ‖A - B‖ * (Real.sqrt N / N) := by ring
    _ = (K : ℝ) * Real.sqrt ((M : ℝ) / N) * ‖A - B‖ := by
      rw [Real.sqrt_div_self, Real.sqrt_div (Nat.cast_nonneg M)]
      ring

lemma mean_convergence_of_bounded_in_probability
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c C : ℝ)
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ C)
    (hprob : TendstoInMeasure μ X atTop (fun _ => c)) :
    Tendsto (fun n => ∫ ω, |X n ω - c| ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms⟩ := (hprob.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n ω => |X (ns (ms n)) ω - c|) (f := fun _ => (0 : ℝ))
    (fun _ => C + |c|)
    (fun n => ((hX _).sub aestronglyMeasurable_const).norm)
    (integrable_const _) ?_ ?_
  · simpa using ht
  · intro n
    filter_upwards [hbound (ns (ms n))] with ω hω
    simp only [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (add_le_add hω le_rfl)
  · filter_upwards [hms] with ω hω
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    simpa using (hω.sub hc).norm

lemma pressure_comp_isometry {M N : ℕ} (A : Disorder M N) (f : ℝ →ᵇ ℝ)
    (V : Vec N ≃ₗᵢ[ℝ] Vec N) :
    pressure (A ∘L V.toContinuousLinearEquiv.toContinuousLinearMap) f = pressure A f := by
  have hi := integral_map_of_stronglyMeasurable (μ := sphereMeasure N)
    V.continuous.measurable (continuous_rowEnergy A f).rexp.stronglyMeasurable
  rw [sphereMeasure_map] at hi
  have hi' :
      (∫ x, Real.exp (rowEnergy (A ∘L V.toContinuousLinearEquiv.toContinuousLinearMap) f x)
        ∂sphereMeasure N) = ∫ x, Real.exp (rowEnergy A f x) ∂sphereMeasure N := by
    simpa only [rowEnergy, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hi.symm
  simp only [pressure, hi']

lemma rowEnergy_activation_error {M N : ℕ} (A : Disorder M N) (f g : ℝ →ᵇ ℝ)
    (ε q : ℝ) (hfg : ∀ t, |f t - g t| ≤ ε + q * t ^ 2) (x : Vec N) :
    |rowEnergy A f x - rowEnergy A g x| ≤ (M : ℝ) * ε + q * ‖A x‖ ^ 2 := by
  calc
    |rowEnergy A f x - rowEnergy A g x| =
        ‖∑ r : Fin M, (f (A x r) - g (A x r))‖ := by
      simp only [rowEnergy, Finset.sum_sub_distrib, Real.norm_eq_abs]
    _ ≤ ∑ r : Fin M, ‖f (A x r) - g (A x r)‖ := norm_sum_le _ _
    _ ≤ ∑ r : Fin M, (ε + q * (A x r) ^ 2) :=
      Finset.sum_le_sum fun r _ => hfg _
    _ = (M : ℝ) * ε + q * ‖A x‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem pressure_activation_error {M N : ℕ} (A : Disorder M N) (f g : ℝ →ᵇ ℝ)
    (ε q : ℝ) (hq : 0 ≤ q) (hfg : ∀ t, |f t - g t| ≤ ε + q * t ^ 2) :
    |pressure A f - pressure A g| ≤ (M : ℝ) / N * ε + q * ‖A‖ ^ 2 := by
  by_cases hN : N = 0
  · subst N
    simp only [pressure, Nat.cast_zero, inv_zero, zero_mul, sub_self, abs_zero,
      div_zero, zero_add]
    positivity
  have hd := log_integral_exp_sub_abs_le (μ := sphereMeasure N)
    (rowEnergy A f) (rowEnergy A g)
    (continuous_rowEnergy A f).aestronglyMeasurable
    (continuous_rowEnergy A g).aestronglyMeasurable
    ((M : ℝ) * max ‖f‖ ‖g‖) ((M : ℝ) * ε + q * ‖A‖ ^ 2 * N)
    (Filter.Eventually.of_forall fun x => (rowEnergy_abs_le A f x).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)))
    (Filter.Eventually.of_forall fun x => (rowEnergy_abs_le A g x).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _))) (by
      filter_upwards [sphereMeasure_norm_sq N] with x hx
      calc
        |rowEnergy A f x - rowEnergy A g x| ≤ (M : ℝ) * ε + q * ‖A x‖ ^ 2 :=
          rowEnergy_activation_error A f g ε q hfg x
        _ ≤ (M : ℝ) * ε + q * (‖A‖ * ‖x‖) ^ 2 := by
          gcongr
          exact A.le_opNorm x
        _ = (M : ℝ) * ε + q * ‖A‖ ^ 2 * N := by rw [mul_pow, hx]; ring)
  calc
    |pressure A f - pressure A g| = (N : ℝ)⁻¹ *
        |Real.log (∫ x, Real.exp (rowEnergy A f x) ∂sphereMeasure N) -
          Real.log (∫ x, Real.exp (rowEnergy A g x) ∂sphereMeasure N)| := by
      rw [pressure, pressure, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
    _ ≤ (N : ℝ)⁻¹ * ((M : ℝ) * ε + q * ‖A‖ ^ 2 * N) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (M : ℝ) / N * ε + q * ‖A‖ ^ 2 := by
      have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      field_simp

lemma activation_error_of_compact_error (f g : ℝ →ᵇ ℝ) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 ≤ ε)
    (hfg : ∀ t ∈ Icc (-R) R, |f t - g t| ≤ ε) (t : ℝ) :
    |f t - g t| ≤ ε + ((‖f‖ + ‖g‖) / R ^ 2) * t ^ 2 := by
  by_cases ht : |t| ≤ R
  · exact (hfg t (abs_le.mp ht)).trans (le_add_of_nonneg_right (by positivity))
  · have hs : R ^ 2 ≤ t ^ 2 := by
      have habs : R < |t| := lt_of_not_ge ht
      nlinarith [sq_abs t]
    have hb : |f t - g t| ≤ ‖f‖ + ‖g‖ := by
      calc
        |f t - g t| ≤ |f t| + |g t| := abs_sub _ _
        _ ≤ ‖f‖ + ‖g‖ := add_le_add (f.norm_coe_le_norm _) (g.norm_coe_le_norm _)
    have hq : ‖f‖ + ‖g‖ ≤ ((‖f‖ + ‖g‖) / R ^ 2) * t ^ 2 := by
      calc
        ‖f‖ + ‖g‖ = ((‖f‖ + ‖g‖) / R ^ 2) * R ^ 2 := by
          rw [div_mul_cancel₀ _ (pow_ne_zero _ hR.ne')]
        _ ≤ ((‖f‖ + ‖g‖) / R ^ 2) * t ^ 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
    exact hb.trans (hq.trans (le_add_of_nonneg_left hε))

theorem pressure_compact_activation_error {M N : ℕ} (A : Disorder M N)
    (f g : ℝ →ᵇ ℝ) (R ε : ℝ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hfg : ∀ t ∈ Icc (-R) R, |f t - g t| ≤ ε) :
    |pressure A f - pressure A g| ≤
      (M : ℝ) / N * ε + ((‖f‖ + ‖g‖) / R ^ 2) * ‖A‖ ^ 2 :=
  pressure_activation_error A f g ε _ (by positivity)
    (activation_error_of_compact_error f g R ε hR hε hfg)

abbrev Sym (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Fields {h : ℕ} (d : Fin h → ℕ) := EuclideanSpace ℝ (Σ j, Fin (d j))

structure MatrixTrial {h : ℕ} (d : Fin h → ℕ) where
  k : ℕ
  ζ : ℕ → ℝ
  q : (j : Fin h) → ℕ → Sym (d j)

def MatrixTrial.increment {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d)
    (j : Fin h) (i : ℕ) : Sym (d j) :=
  T.q j i - if i = 0 then 0 else T.q j (i - 1)

def MatrixTrial.K {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d)
    (j : Fin h) (i : ℕ) : Sym (d j) :=
  ∑ r ∈ Finset.Icc (i + 1) T.k, T.ζ r • T.increment j r

def MatrixTrial.Active {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d)
    (θ : ℝ) (j : Fin h) (i : ℕ) :=
  {a : Fin (d j) // i < T.k ∧ (T.ζ i < θ ∨ a.val ≠ 0)}

instance {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d) (θ : ℝ) (j : Fin h) (i : ℕ) :
    Fintype (T.Active θ j i) := by
  classical
  unfold MatrixTrial.Active
  exact Fintype.ofFinite _

instance {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d) (θ : ℝ) (j : Fin h) (i : ℕ) :
    DecidableEq (T.Active θ j i) := Classical.decEq _

def MatrixTrial.compression {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d) (θ : ℝ)
    (j : Fin h) (i : ℕ) (Q : Sym (d j)) :
    Matrix (T.Active θ j i) (T.Active θ j i) ℝ :=
  Q.submatrix Subtype.val Subtype.val

def MatrixTrial.baseline {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d) (θ : ℝ) :
    MatrixTrial d :=
  { T with q := fun j i => if i = T.k then 1 else
      Matrix.diagonal (fun a : Fin (d j) => if θ ≤ T.ζ i ∧ a.val = 0 then 1 else 0) }

def MatrixTrial.Eligible {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d) (θ : ℝ) : Prop :=
  0 < T.k ∧ T.ζ 0 = 0 ∧ T.ζ T.k = 1 ∧
  (∀ i < T.k, T.ζ i < T.ζ (i + 1)) ∧
  (∃ i ≤ T.k, T.ζ i = θ) ∧
  (∀ j, T.q j T.k = 1) ∧
  (∀ j i, i ≤ T.k → (T.increment j i).PosSemidef) ∧
  (∀ j i, i ≤ T.k → θ ≤ T.ζ i →
    ∀ a b : Fin (d j), b.val = 0 → T.q j i a b = if a = b then 1 else 0) ∧
  (∀ j i, i < T.k → (T.compression θ j i (T.K j i)).PosDef)

def MatrixTrial.entropy {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d)
    (θ : ℝ) (j : Fin h) : ℝ :=
  let detK := fun i => (T.compression θ j i (T.K j i)).det
  let detK₀ := fun i => (T.compression θ j i ((T.baseline θ).K j i)).det
  (Matrix.trace ((T.K j 0)⁻¹ * T.q j 0) +
    ∑ i ∈ Finset.Icc 1 T.k, (T.ζ i)⁻¹ *
      Real.log ((detK (i - 1) / detK i) * (detK₀ i / detK₀ (i - 1)))) / 2

def matrixGaussianStep {h : ℕ} {d : Fin h → ℕ} (z : ℝ)
    (C : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) ℝ)
    (U : Fields d → ℝ) (x : Fields d) : ℝ :=
  if z = 0 then ∫ y, U (x + y) ∂multivariateGaussian 0 C
  else z⁻¹ * Real.log (∫ y, Real.exp (z * U (x + y)) ∂multivariateGaussian 0 C)

def MatrixTrial.value {h : ℕ} {d : Fin h → ℕ} (T : MatrixTrial d)
    (D : Fields d → ℝ) : ℝ :=
  ((List.range (T.k + 1)).reverse.foldl
    (fun U i => matrixGaussianStep (T.ζ i)
      (Matrix.blockDiagonal' (fun j => T.increment j i)) U) D) 0

def gaussianValues {h : ℕ} {d : Fin h → ℕ} (θ : ℝ) (p : Fin h → ℝ)
    (D : Fields d → ℝ) : Set ℝ :=
  {v | ∃ T : MatrixTrial d, T.Eligible θ ∧
    v = (∑ j, p j * T.entropy θ j) + T.value D}

def gaussianFunctional {h : ℕ} {d : Fin h → ℕ} (θ : ℝ) (p : Fin h → ℝ)
    (D : Fields d → ℝ) : ℝ := sInf (gaussianValues θ p D)

def GaussianWellDefined {h : ℕ} {d : Fin h → ℕ} (θ : ℝ) (p : Fin h → ℝ)
    (D : Fields d → ℝ) : Prop :=
  (gaussianValues θ p D).Nonempty ∧ BddBelow (gaussianValues θ p D)

def angularDim {h : ℕ} (j : Fin h) : ℕ := h - j.val
abbrev Coefficients (h : ℕ) := (j : Fin h) → Sym (angularDim j)

def Coefficients.Admissible {h : ℕ} (R : Coefficients h) (κ : ℝ) : Prop :=
  (∀ j (r c : Fin (angularDim j)), c < r → R j r c = 0) ∧
  (∀ j (c : Fin (angularDim j)), 0 < R j c c) ∧
  (∀ j (c : Fin (angularDim j)),
    ‖(WithLp.toLp 2 (fun r => R j r c) : Vec (angularDim j))‖ ≤ κ)

def coefficientField {h : ℕ} (R : Coefficients h) (ξ : Fields (@angularDim h))
    (j : Fin h) (c : Fin (angularDim j)) : ℝ :=
  ∑ r, ξ ⟨j, r⟩ * R j r c

def yField {h : ℕ} (R : Coefficients h) (ξ : Fields (@angularDim h)) : ℝ :=
  ∑ j, coefficientField R ξ j ⟨0, Nat.sub_pos_of_lt j.isLt⟩

def uField {h : ℕ} (R : Coefficients h) (ξ : Fields (@angularDim h))
    (i : Fin (h - 1)) : ℝ :=
  ∑ j : Fin h, if hji : j.val ≤ i.val then
    coefficientField R ξ j ⟨i.val - j.val + 1, by
      have hi := i.isLt
      unfold angularDim
      omega⟩ else 0

def rowTests {h : ℕ} (R : Coefficients h) (B : ℝ) (ξ : Fields (@angularDim h))
    (l : Fin (h + 1)) : ℝ :=
  if hl : l.val = 0 then (yField R ξ) ^ 2
  else if hl' : l.val = 1 then -min ((yField R ξ) ^ 2) B
  else (yField R ξ - uField R ξ ⟨l.val - 2, by have := l.isLt; omega⟩) ^ 2

def testConstants {h : ℕ} (a : Fin h → ℝ) (l : Fin (h + 1)) : ℝ :=
  if l.val = 0 then ∑ j, a j
  else if l.val = 1 then -(∑ j, a j)
  else ∑ j : Fin h, if l.val - 2 < j.val then a j else 0

def penaltyTerminal {h : ℕ} (f : ℝ →ᵇ ℝ) (R : Coefficients h) (B θ : ℝ)
    (t : Fin (h + 1) → ℝ) (ξ : Fields (@angularDim h)) : ℝ :=
  f (yField R ξ) / θ - ∑ l, t l * rowTests R B ξ l

def penaltyBox (h : ℕ) (lam θ : ℝ) : Set (Fin (h + 1) → ℝ) :=
  {t | ∀ l, 0 ≤ t l ∧ t l ≤ lam / θ}

def penaltyValue {h : ℕ} (p a : Fin h → ℝ) (f : ℝ →ᵇ ℝ)
    (R : Coefficients h) (B θ : ℝ) (t : Fin (h + 1) → ℝ) : ℝ :=
  (∑ l, t l * testConstants a l) + gaussianFunctional θ p (penaltyTerminal f R B θ t)

def coefficientEntropy {h : ℕ} (p : Fin h → ℝ) (R : Coefficients h)
    (κ θ : ℝ) : ℝ :=
  ∑ j, p j * (Real.log (κ * Real.sqrt (2 * Real.pi * Real.exp 1 / p j)) +
    Real.log (R j ⟨0, Nat.sub_pos_of_lt j.isLt⟩ ⟨0, Nat.sub_pos_of_lt j.isLt⟩ / κ) +
    θ * ∑ l : Fin (angularDim j), if 0 < l.val then Real.log (R j l l / κ) else 0)

def coefficientValues {h : ℕ} (p a : Fin h → ℝ) (f : ℝ →ᵇ ℝ)
    (κ lam B θ : ℝ) : Set ℝ :=
  {v | ∃ R : Coefficients h, R.Admissible κ ∧ v = coefficientEntropy p R κ θ +
    θ * sInf (penaltyValue p a f R B θ '' penaltyBox h lam θ)}

def coefficientFunctional {h : ℕ} (p a : Fin h → ℝ) (f : ℝ →ᵇ ℝ)
    (κ lam B θ : ℝ) : ℝ := sSup (coefficientValues p a f κ lam B θ)

def CoefficientWellDefined {h : ℕ} (p a : Fin h → ℝ) (f : ℝ →ᵇ ℝ)
    (κ lam B θ : ℝ) : Prop :=
  (coefficientValues p a f κ lam B θ).Nonempty ∧
  BddAbove (coefficientValues p a f κ lam B θ) ∧
  ∀ R : Coefficients h, R.Admissible κ →
    (∀ t ∈ penaltyBox h lam θ, GaussianWellDefined θ p (penaltyTerminal f R B θ t)) ∧
    ∃ t ∈ penaltyBox h lam θ, ∀ t' ∈ penaltyBox h lam θ,
      penaltyValue p a f R B θ t ≤ penaltyValue p a f R B θ t'

def shellEntropy {h : ℕ} (p a : Fin h → ℝ) : ℝ :=
  (∑ j, p j * Real.log (2 * Real.pi * Real.exp 1 * a j / p j)) / 2

def haarJacobian {h : ℕ} (p : Fin h → ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..(∑ j, p j), Real.log (1 - u)) / 2

abbrev AngularFamily := (h : ℕ) → (Fin h → ℝ) → (Fin h → ℝ) → ℝ

def PositiveProportions {h : ℕ} (p : Fin h → ℝ) : Prop :=
  0 < h ∧ (∀ j, 0 < p j) ∧ (∑ j, p j) ≤ 1

def AngularFormula (f : ℝ →ᵇ ℝ) (P : AngularFamily) : Prop :=
  (∀ h (p : Fin h → ℝ), PositiveProportions p →
    ContinuousOn (P h p) {a | ∀ j, 0 ≤ a j}) ∧
  (∀ h (p a : Fin h → ℝ) (σ : Equiv.Perm (Fin h)), PositiveProportions p →
    (∀ j, 0 ≤ a j) → P h (p ∘ σ) (a ∘ σ) = P h p a) ∧
  (∀ h (p a : Fin h → ℝ), PositiveProportions p → (∑ j, p j) < 1 →
    (∀ j, 0 < a j) → Antitone (fun j => a j / p j) →
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ, κ₀ ≤ κ →
      (∀ lam > 0, ∀ B > 0, ∀ θ ∈ Ioo (0 : ℝ) 1,
        CoefficientWellDefined p a f κ lam B θ) ∧
      ∃ L : ℝ → ℝ → ℝ, ∃ L' : ℝ → ℝ,
        (∀ lam > 0, ∀ B > 0,
          Tendsto (fun θ => coefficientFunctional p a f κ lam B θ) (𝓝[>] 0) (𝓝 (L lam B))) ∧
        (∀ lam > 0, Tendsto (L lam) atTop (𝓝 (L' lam))) ∧
        Tendsto L' atTop (𝓝 (P h p a - haarJacobian p + shellEntropy p a))) ∧
  (∀ h (p a : Fin h → ℝ), PositiveProportions p → (∑ j, p j) = 1 →
    (∀ j, 0 ≤ a j) →
    Tendsto (fun η => P h (fun j => (1 - η) * p j) a) (𝓝[>] 0) (𝓝 (P h p a)))

structure FiniteSpectrum (α : ℝ) where
  h : ℕ
  h_pos : 0 < h
  p : Fin h → ℝ
  p_pos : ∀ j, 0 < p j
  sum_p : (∑ j, p j) = min 1 (1 / α)
  s : Fin h → ℝ
  s_pos : ∀ j, 0 < s j

def InputBlocks (α : ℝ) (h : ℕ) :=
  {i : Option (Fin h) // i ≠ none ∨ α < 1}

instance (α : ℝ) (h : ℕ) : Fintype (InputBlocks α h) := by
  classical
  unfold InputBlocks
  exact Fintype.ofFinite _

instance (α : ℝ) (h : ℕ) : DecidableEq (InputBlocks α h) := Classical.decEq _

def finiteBlock {α : ℝ} (S : FiniteSpectrum α) (j : Fin S.h) : InputBlocks α S.h :=
  ⟨some j, Or.inl (by simp)⟩

def inputWeights {α : ℝ} (S : FiniteSpectrum α) (i : InputBlocks α S.h) : ℝ :=
  match i.val with
  | none => 1 - α
  | some j => α * S.p j

def openSimplex (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {ρ | (∀ i, 0 < ρ i) ∧ (∑ i, ρ i) = 1}

def radialObjective {α : ℝ} (P : AngularFamily) (S : FiniteSpectrum α)
    (ρ : InputBlocks α S.h → ℝ) : ℝ :=
  (∑ i, inputWeights S i * Real.log (ρ i / inputWeights S i)) / 2 +
    α * P S.h S.p (fun j => (S.s j) ^ 2 * ρ (finiteBlock S j) / α)

def radialValue {α : ℝ} (P : AngularFamily) (S : FiniteSpectrum α) : ℝ :=
  sSup (radialObjective P S '' openSimplex (InputBlocks α S.h))

def RadialWellDefined {α : ℝ} (P : AngularFamily) (S : FiniteSpectrum α) : Prop :=
  (openSimplex (InputBlocks α S.h)).Nonempty ∧
    BddAbove (radialObjective P S '' openSimplex (InputBlocks α S.h))

def outputDimension (α : ℝ) (N : ℕ) : ℕ := ⌊α * N⌋₊
def slotCount (α : ℝ) (N : ℕ) : ℕ := min (outputDimension α N) N

def singularSlots {M N : ℕ} (A : Disorder M N) (r : Fin (min M N)) : ℝ :=
  A.toLinearMap.singularValues r.val

def BiOrthogonallyInvariant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {M N : ℕ} (A : Ω → Disorder M N) : Prop :=
  ∀ (U : Vec M ≃ₗᵢ[ℝ] Vec M) (V : Vec N ≃ₗᵢ[ℝ] Vec N),
    μ.map (fun ω => U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (A ω ∘L V.toContinuousLinearEquiv.toContinuousLinearMap)) = μ.map A

def empiricalAverage {M N : ℕ} (A : Disorder M N) (g : ℝ →ᵇ ℝ) : ℝ :=
  ((min M N : ℕ) : ℝ)⁻¹ * ∑ r : Fin (min M N), g (singularSlots A r)

def outlierError {M N : ℕ} (A : Disorder M N) (ν : ProbabilityMeasure ℝ) : ℝ :=
  ((Finset.univ.sup (fun r : Fin (min M N) =>
    Real.toNNReal (Metric.infDist (singularSlots A r) (ν : Measure ℝ).support))) : NNReal)

def SpectralHypotheses {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (α : ℝ) (ν : ProbabilityMeasure ℝ) (A : (N : ℕ) → Ω → Disorder (outputDimension α N) N) : Prop :=
  (∀ g : ℝ →ᵇ ℝ, TendstoInMeasure μ (fun N ω => empiricalAverage (A N ω) g)
    atTop (fun _ => ∫ x, g x ∂(ν : Measure ℝ))) ∧
  TendstoInMeasure μ (fun N ω => outlierError (A N ω) ν) atTop (fun _ => 0)

def PressureConverges {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (α : ℝ) (A : (N : ℕ) → Ω → Disorder (outputDimension α N) N) (f : ℝ →ᵇ ℝ) (F : ℝ) : Prop :=
  TendstoInMeasure μ (fun N ω => pressure (A N ω) f) atTop (fun _ => F) ∧
  Tendsto (fun N => ∫ ω, |pressure (A N ω) f - F| ∂μ) atTop (𝓝 0)

structure SpectralMesh (α : ℝ) (ν : ProbabilityMeasure ℝ) (δ : ℝ) extends FiniteSpectrum α where
  cell : ℝ → Fin h
  cell_measurable : Measurable cell
  cell_mass_pos : ∀ j, 0 < (ν : Measure ℝ).real {x | cell x = j}
  p_eq_mass : ∀ j, p j = min 1 (1 / α) * (ν : Measure ℝ).real {x | cell x = j}
  boundary_null : ∀ j, (ν : Measure ℝ) (frontier {x | cell x = j}) = 0
  mesh_error : ∀ x : ℝ, 0 ≤ x →
    |x - s (cell x)| ≤ δ + Metric.infDist x (ν : Measure ℝ).support

def meshMultiplicity {α δ : ℝ} {ν : ProbabilityMeasure ℝ} (Q : SpectralMesh α ν δ)
    {M N : ℕ} (A : Disorder M N) (j : Fin Q.h) : ℕ :=
  (Finset.univ.filter (fun r : Fin (min M N) => Q.cell (singularSlots A r) = j)).card

def slotDiagonal (M N : ℕ) (s : Fin (min M N) → ℝ) : Disorder M N :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    (fun (i : Fin M) (j : Fin N) => if hij : i.val = j.val then
      s ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ else 0))

def HasMeshApproximation {α δ : ℝ} {ν : ProbabilityMeasure ℝ} (Q : SpectralMesh α ν δ)
    {M N : ℕ} (A : Disorder M N) : Prop :=
  ∃ (U : Vec M ≃ₗᵢ[ℝ] Vec M) (V : Vec N ≃ₗᵢ[ℝ] Vec N),
    A = U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (slotDiagonal M N (singularSlots A) ∘L V.toContinuousLinearEquiv.toContinuousLinearMap) ∧
    ‖A - U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (slotDiagonal M N (fun r => Q.s (Q.cell (singularSlots A r))) ∘L
        V.toContinuousLinearEquiv.toContinuousLinearMap)‖ ≤ δ + outlierError A ν

def MeshApproximates {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (α : ℝ) (ν : ProbabilityMeasure ℝ) (A : (N : ℕ) → Ω → Disorder (outputDimension α N) N)
    {δ : ℝ} (Q : SpectralMesh α ν δ) : Prop :=
  (∀ j, TendstoInMeasure μ
    (fun N ω => (meshMultiplicity Q (A N ω) j : ℝ) / outputDimension α N)
    atTop (fun _ => Q.p j)) ∧
  (∀ N ω, HasMeshApproximation Q (A N ω))

def HasFiniteSlots {α : ℝ} (S : FiniteSpectrum α) {M N : ℕ}
    (A : Disorder M N) (n : Fin S.h → ℕ) : Prop :=
  (List.ofFn (singularSlots A) : Multiset ℝ) = ∑ j : Fin S.h, Multiset.replicate (n j) (S.s j)

def FiniteRadialLimit (α : ℝ) (f : ℝ →ᵇ ℝ) (P : AngularFamily) : Prop :=
  ∀ S : FiniteSpectrum α, RadialWellDefined P S ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A : (N : ℕ) → Ω → Disorder (outputDimension α N) N)
      (n : ℕ → Fin S.h → ℕ),
      (∀ N, Measurable (A N)) →
      (∀ N, BiOrthogonallyInvariant μ (A N)) →
      (∀ N, (∑ j, n N j) = slotCount α N) →
      (∀ j, Tendsto (fun N => (n N j : ℝ) / outputDimension α N) atTop (𝓝 (S.p j))) →
      (∀ N, ∀ᵐ ω ∂μ, HasFiniteSlots S (A N ω) (n N)) →
      PressureConverges μ α A f (radialValue P S)

def SpectralMeshLimit (α : ℝ) (ν : ProbabilityMeasure ℝ) (P : AngularFamily) (F : ℝ) : Prop :=
  (∀ δ > 0, Nonempty (SpectralMesh α ν δ)) ∧
  ∀ (δ : ℕ → ℝ), (∀ k, 0 < δ k) → Tendsto δ atTop (𝓝 0) →
    ∀ Q : (k : ℕ) → SpectralMesh α ν (δ k),
      Tendsto (fun k => radialValue P (Q k).toFiniteSpectrum) atTop (𝓝 F)

lemma pressure_uniform_bound (α : ℝ) (hα : 0 ≤ α) (N : ℕ)
    (A : Disorder (outputDimension α N) N) (f : ℝ →ᵇ ℝ) :
    |pressure A f| ≤ α * ‖f‖ := by
  by_cases hN : N = 0
  · subst N
    simp only [pressure, Nat.cast_zero, inv_zero, zero_mul, abs_zero]
    positivity
  · have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hf : (outputDimension α N : ℝ) ≤ α * N :=
      Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg N))
    exact (pressure_abs_le A f).trans
      (mul_le_mul_of_nonneg_right ((div_le_iff₀ hN').mpr hf) (norm_nonneg _))

theorem pressure_converges_of_in_probability
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ)
    (A : (N : ℕ) → Ω → Disorder (outputDimension α N) N)
    (hA : ∀ N, Measurable (A N)) (F : ℝ)
    (hprob : TendstoInMeasure μ (fun N ω => pressure (A N ω) f) atTop (fun _ => F)) :
    PressureConverges μ α A f F := by
  refine ⟨hprob, mean_convergence_of_bounded_in_probability _ F (α * ‖f‖) ?_ ?_ hprob⟩
  · intro N
    exact ((continuous_pressure f).measurable.comp (hA N)).aestronglyMeasurable
  · intro N
    exact Filter.Eventually.of_forall (fun ω => pressure_uniform_bound α hα N (A N ω) f)

end SphericalPerceptron.InvariantDisorder

end

end OAI
