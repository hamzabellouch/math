import OAI.Probability.FreeIsing.Posterior.GaussianTimeDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal

namespace Problem367

theorem hasDerivAt_integral_sqrt_observation_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {S G : Ω → ℝ} (hS : Integrable S P) (hG : Integrable G P)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'm : Measurable f')
    {M : ℝ} (hM : 0 ≤ M)
    (hf'bound : ∀ x, |f' x| ≤ M) {t : ℝ} (ht : 0 < t)
    (hFint : Integrable (fun ω => f (t * S ω + Real.sqrt t * G ω)) P) :
    Integrable (fun ω => f' (t * S ω + Real.sqrt t * G ω) *
      (S ω + G ω / (2 * Real.sqrt t))) P ∧
    HasDerivAt (fun r : ℝ => ∫ ω, f (r * S ω + Real.sqrt r * G ω) ∂P)
      (∫ ω, f' (t * S ω + Real.sqrt t * G ω) *
        (S ω + G ω / (2 * Real.sqrt t)) ∂P) t := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hf x).continuousAt)
  let F : ℝ → Ω → ℝ := fun r ω => f (r * S ω + Real.sqrt r * G ω)
  let F' : ℝ → Ω → ℝ := fun r ω => f' (r * S ω + Real.sqrt r * G ω) *
    (S ω + G ω / (2 * Real.sqrt r))
  let a : ℝ := 1 / (2 * Real.sqrt (t / 2))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hFm (r : ℝ) : AEStronglyMeasurable (F r) P :=
    hfcont.comp_aestronglyMeasurable
      ((hS.aestronglyMeasurable.const_mul r).add
        (hG.aestronglyMeasurable.const_mul (Real.sqrt r)))
  have hF'm (r : ℝ) : AEStronglyMeasurable (F' r) P := by
    apply AEStronglyMeasurable.mul
    · exact (hf'm.comp_aemeasurable
        ((hS.aemeasurable.const_mul r).add
          (hG.aemeasurable.const_mul (Real.sqrt r)))).aestronglyMeasurable
    · simpa only [div_eq_mul_inv, Pi.add_def] using hS.aestronglyMeasurable.add
        (hG.aestronglyMeasurable.mul_const (2 * Real.sqrt r)⁻¹)
  have hdom : Integrable (fun ω => M * (|S ω| + a * |G ω|)) P :=
    (hS.abs.add (hG.abs.const_mul a)).const_mul M
  have hbound : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2),
      ‖F' r ω‖ ≤ M * (|S ω| + a * |G ω|) := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have hden : 0 < 2 * Real.sqrt (t / 2) := by positivity
    have hrecip : 1 / (2 * Real.sqrt r) ≤ a := by
      apply one_div_le_one_div_of_le hden
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.le) (by norm_num)
    have hinner : |S ω + G ω / (2 * Real.sqrt r)| ≤ |S ω| + a * |G ω| := by
      calc
        _ ≤ |S ω| + |G ω / (2 * Real.sqrt r)| := abs_add_le _ _
        _ = |S ω| + (1 / (2 * Real.sqrt r)) * |G ω| := by
          rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt r)]
          ring
        _ ≤ |S ω| + a * |G ω| := by gcongr
    dsimp [F']
    rw [abs_mul]
    exact mul_le_mul (hf'bound _) hinner (abs_nonneg _) hM
  have hdiff : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2), HasDerivAt (fun q => F q ω) (F' r ω) r := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have harg := ((hasDerivAt_id r).mul_const (S ω)).add
      ((Real.hasDerivAt_sqrt hrpos.ne').mul_const (G ω))
    have harg' : HasDerivAt (fun q : ℝ => q * S ω + Real.sqrt q * G ω)
        (S ω + G ω / (2 * Real.sqrt r)) r := by
      simpa only [Pi.add_def, id_eq, one_mul, mul_one, one_div, div_eq_mul_inv, mul_comm] using harg
    exact (hf (r * S ω + Real.sqrt r * G ω)).comp r harg'
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall hFm) hFint (hF'm t) hbound hdom hdiff

theorem hasDerivAt_integral_sqrt_observation_vector_of_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P]
    {S G : Ω → E} (hS : Integrable S P) (hG : Integrable G P)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf'cont : Continuous f')
    {M : ℝ} (hM : 0 ≤ M)
    (hf'bound : ∀ x, ‖f' x‖ ≤ M) {t : ℝ} (ht : 0 < t)
    (hFint : Integrable (fun ω => f (t • S ω + Real.sqrt t • G ω)) P) :
    Integrable (fun ω => f' (t • S ω + Real.sqrt t • G ω)
      (S ω + (1 / (2 * Real.sqrt t)) • G ω)) P ∧
    HasDerivAt (fun r : ℝ => ∫ ω, f (r • S ω + Real.sqrt r • G ω) ∂P)
      (∫ ω, f' (t • S ω + Real.sqrt t • G ω)
        (S ω + (1 / (2 * Real.sqrt t)) • G ω) ∂P) t := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hf x).continuousAt)
  let F : ℝ → Ω → ℝ := fun r ω => f (r • S ω + Real.sqrt r • G ω)
  let F' : ℝ → Ω → ℝ := fun r ω => f' (r • S ω + Real.sqrt r • G ω)
    (S ω + (1 / (2 * Real.sqrt r)) • G ω)
  let a : ℝ := 1 / (2 * Real.sqrt (t / 2))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hargm (r : ℝ) : AEStronglyMeasurable
      (fun ω => r • S ω + Real.sqrt r • G ω) P :=
    (hS.aestronglyMeasurable.const_smul r).add
      (hG.aestronglyMeasurable.const_smul (Real.sqrt r))
  have hFm (r : ℝ) : AEStronglyMeasurable (F r) P :=
    hfcont.comp_aestronglyMeasurable (hargm r)
  have hF'm (r : ℝ) : AEStronglyMeasurable (F' r) P :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous
      |>.comp_aestronglyMeasurable
        ((hf'cont.comp_aestronglyMeasurable (hargm r)).prodMk
          (hS.aestronglyMeasurable.add
            (hG.aestronglyMeasurable.const_smul (1 / (2 * Real.sqrt r)))))
  have hdom : Integrable (fun ω => M * (‖S ω‖ + a * ‖G ω‖)) P :=
    (hS.norm.add (hG.norm.const_mul a)).const_mul M
  have hbound : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2),
      ‖F' r ω‖ ≤ M * (‖S ω‖ + a * ‖G ω‖) := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have hden : 0 < 2 * Real.sqrt (t / 2) := by positivity
    have hrecip : 1 / (2 * Real.sqrt r) ≤ a := by
      apply one_div_le_one_div_of_le hden
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.le) (by norm_num)
    have hinner : ‖S ω + (1 / (2 * Real.sqrt r)) • G ω‖ ≤
        ‖S ω‖ + a * ‖G ω‖ := by
      calc
        _ ≤ ‖S ω‖ + ‖(1 / (2 * Real.sqrt r)) • G ω‖ := norm_add_le _ _
        _ = ‖S ω‖ + (1 / (2 * Real.sqrt r)) * ‖G ω‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ ‖S ω‖ + a * ‖G ω‖ := by gcongr
    exact ((f' (r • S ω + Real.sqrt r • G ω)).le_opNorm _).trans
      (mul_le_mul (hf'bound _) hinner (norm_nonneg _) hM)
  have hdiff : ∀ᵐ ω ∂P, ∀ r ∈ Ioi (t / 2),
      HasDerivAt (fun q => F q ω) (F' r ω) r := by
    filter_upwards [] with ω
    intro r hr
    have hrpos : 0 < r := lt_trans (by linarith) hr
    have harg := ((hasDerivAt_id r).smul_const (S ω)).add
      ((Real.hasDerivAt_sqrt hrpos.ne').smul_const (G ω))
    have harg' : HasDerivAt (fun q : ℝ => q • S ω + Real.sqrt q • G ω)
        (S ω + (1 / (2 * Real.sqrt r)) • G ω) r := by
      simpa only [Pi.add_def, id_eq, one_smul, one_div] using harg
    exact (hf (r • S ω + Real.sqrt r • G ω)).comp_hasDerivAt r harg'
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall hFm) hFint (hF'm t) hbound hdom hdiff

theorem continuous_integral_sqrt_observation_lipschitz
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {S G : Ω → E}
    (hS : Integrable S P) (hG : Integrable G P)
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Continuous (fun t : ℝ => ∫ ω, f (t • S ω + Real.sqrt t • G ω) ∂P) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let a : ℝ := |t| + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hloc : ∀ᶠ r in 𝓝 t, |r| < a :=
    continuous_abs.continuousAt.eventually
      (gt_mem_nhds (by dsimp [a]; linarith : |t| < a))
  apply continuousAt_of_dominated
    (bound := fun ω => ‖f 0‖ + (K : ℝ) *
      (a * ‖S ω‖ + Real.sqrt a * ‖G ω‖))
  · exact Eventually.of_forall fun r => hf.continuous.comp_aestronglyMeasurable
      ((hS.aestronglyMeasurable.const_smul r).add
        (hG.aestronglyMeasurable.const_smul (Real.sqrt r)))
  · filter_upwards [hloc] with r hr
    exact Eventually.of_forall fun ω => by
      have harg : ‖r • S ω + Real.sqrt r • G ω‖ ≤
          a * ‖S ω‖ + Real.sqrt a * ‖G ω‖ := by
        calc
          _ ≤ ‖r • S ω‖ + ‖Real.sqrt r • G ω‖ := norm_add_le _ _
          _ = |r| * ‖S ω‖ + Real.sqrt r * ‖G ω‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg r)]
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_right hr.le (norm_nonneg _))
            (mul_le_mul_of_nonneg_right
              (Real.sqrt_le_sqrt ((le_abs_self r).trans hr.le)) (norm_nonneg _))
      calc
        _ ≤ ‖f 0‖ + ‖f (r • S ω + Real.sqrt r • G ω) - f 0‖ :=
          norm_le_norm_add_norm_sub' _ _
        _ ≤ ‖f 0‖ + (K : ℝ) * ‖r • S ω + Real.sqrt r • G ω‖ := by
          gcongr
          simpa only [sub_zero] using hf.norm_sub_le
            (r • S ω + Real.sqrt r • G ω) 0
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left harg K.coe_nonneg)
  · exact (integrable_const ‖f 0‖).add
      (((hS.norm.const_mul a).add (hG.norm.const_mul (Real.sqrt a))).const_mul (K : ℝ))
  · exact Eventually.of_forall fun ω => (hf.continuous.comp
      ((continuous_id.smul continuous_const).add
        (Real.continuous_sqrt.smul continuous_const))).continuousAt

theorem tendsto_integral_sqrt_observation_zero_lipschitz
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {S G : Ω → E}
    (hS : Integrable S P) (hG : Integrable G P)
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Tendsto (fun t : ℝ => ∫ ω, f (t • S ω + Real.sqrt t • G ω) ∂P)
      (𝓝 0) (𝓝 (P.real Set.univ * f 0)) := by
  simpa only [zero_smul, Real.sqrt_zero, zero_add, integral_const, smul_eq_mul] using
    (continuous_integral_sqrt_observation_lipschitz hS hG hf).tendsto 0

namespace FinitePosterior

variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω]

theorem hasDerivAt_integral_gaussianObservationCurve_of_integrable
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : (V → ℝ) → ℝ) (g : (V → ℝ) → V → ℝ)
    (hdf : ∀ x, HasFDerivAt f (∑ v, g x v •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x)
    (hg : ∀ v, Continuous (fun x => g x v))
    (C : ℝ) (hC : 0 ≤ C) (hgbound : ∀ x v, |g x v| ≤ C)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t)
    (hFint : Integrable (fun ω =>
      f (gaussianObservationCurve (signal ω) (noise ω) t)) μ) :
    HasDerivAt (fun r => ∫ ω, f (gaussianObservationCurve (signal ω) (noise ω) r) ∂μ)
      (∫ ω, ∑ v, g (gaussianObservationCurve (signal ω) (noise ω) t) v *
        gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  let D : (V → ℝ) → (V → ℝ) →L[ℝ] ℝ := fun x => ∑ v, g x v •
    (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)
  have hDcont : Continuous D := by
    apply continuous_finsetSum
    intro v _
    exact (hg v).smul continuous_const
  have hDbound (x : V → ℝ) : ‖D x‖ ≤ (Fintype.card V : ℝ) * C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hC)
    intro y
    simp only [D, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    calc
      ‖∑ v, g x v * y v‖ ≤ ∑ v, ‖g x v * y v‖ := norm_sum_le _ _
      _ ≤ ∑ v : V, C * ‖y‖ := by
        apply Finset.sum_le_sum
        intro v _
        rw [norm_mul, Real.norm_eq_abs (g x v)]
        exact mul_le_mul (hgbound x v) (norm_le_pi_norm y v) (norm_nonneg _) hC
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hsInt : Integrable signal μ := Integrable.of_eval fun v =>
    Integrable.of_bound ((measurable_pi_apply v).comp hsignal).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hspin ω v)
  have hnInt : Integrable noise μ :=
    ⟨hnoise.aestronglyMeasurable, (Integrable.of_eval hnoiseInt).hasFiniteIntegral⟩
  have hd := (hasDerivAt_integral_sqrt_observation_vector_of_integrable hsInt hnInt hdf hDcont
    (mul_nonneg (by positivity) hC) hDbound ht hFint).2
  simpa only [gaussianObservationCurve, gaussianObservationVelocity, D, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using hd

end FinitePosterior

end Problem367

end

end OAI
