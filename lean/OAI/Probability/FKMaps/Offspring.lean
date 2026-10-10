import OAI.Probability.FKMaps.PathCLT

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

structure CriticalEvenOffspring where
  mass : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ mass k
  total : HasSum mass 1
  even_support : ∀ k, Odd k → mass k = 0
  zero_pos : 0 < mass 0
  two_pos : 0 < mass 2
  mean : HasSum (fun k : ℕ => (k : ℝ) * mass k) 1
  second : Summable (fun k : ℕ => (k : ℝ)^2 * mass k)


def CriticalEvenOffspring.variance (p : CriticalEvenOffspring) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) - 1)^2 * p.mass k


def CriticalEvenOffspring.sigma (p : CriticalEvenOffspring) : ℝ :=
  Real.sqrt p.variance


lemma CriticalEvenOffspring.summable_variance (p : CriticalEvenOffspring) :
    Summable (fun k : ℕ => ((k : ℝ) - 1)^2 * p.mass k) := by
  apply Summable.of_nonneg_of_le (fun k : ℕ => mul_nonneg (sq_nonneg _) (p.nonneg k))
    (f := fun k : ℕ => (k : ℝ)^2 * p.mass k + p.mass k)
  · intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [p.nonneg k, mul_nonneg hk (p.nonneg k)]
  · exact p.second.add p.total.summable


lemma CriticalEvenOffspring.variance_pos (p : CriticalEvenOffspring) : 0 < p.variance := by
  have hle := p.summable_variance.le_tsum 0
    (fun k _ => mul_nonneg (sq_nonneg _) (p.nonneg k))
  simp only [Nat.cast_zero, zero_sub, neg_sq, one_pow, one_mul] at hle
  exact p.zero_pos.trans_le hle


lemma CriticalEvenOffspring.sigma_pos (p : CriticalEvenOffspring) : 0 < p.sigma :=
  Real.sqrt_pos.mpr p.variance_pos


def CriticalEvenOffspring.law (p : CriticalEvenOffspring) : PMF ℕ :=
  ⟨fun k => ((NNReal.mk (p.mass k) (p.nonneg k)) : ℝ≥0∞), by
    apply ENNReal.hasSum_coe.mpr
    apply NNReal.hasSum_coe.mp
    exact p.total⟩


@[simp] lemma CriticalEvenOffspring.law_apply (p : CriticalEvenOffspring) (k : ℕ) :
    p.law k = ENNReal.ofReal (p.mass k) := by
  rw [ENNReal.ofReal_eq_coe_nnreal (p.nonneg k)]
  rfl


@[simp] lemma CriticalEvenOffspring.law_singleton (p : CriticalEvenOffspring) (k : ℕ) :
    p.law.toMeasure {k} = ENNReal.ofReal (p.mass k) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k), p.law_apply]


@[simp] lemma CriticalEvenOffspring.law_real_singleton (p : CriticalEvenOffspring) (k : ℕ) :
    p.law.toMeasure.real {k} = p.mass k := by
  simp [measureReal_def, p.nonneg]


lemma CriticalEvenOffspring.integrable_iff {E : Type*} [NormedAddCommGroup E]
    (p : CriticalEvenOffspring) (f : ℕ → E) :
    Integrable f p.law.toMeasure ↔ Summable (fun k => p.mass k * ‖f k‖) := by
  rw [← Measure.sum_smul_dirac p.law.toMeasure, integrable_sum_dirac_iff]
  · simp only [p.law_singleton, ENNReal.toReal_ofReal (p.nonneg _)]
  · intro k
    simp


lemma CriticalEvenOffspring.integral_eq_tsum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : CriticalEvenOffspring) (f : ℕ → E)
    (hf : Summable (fun k => p.mass k * ‖f k‖)) :
    ∫ k, f k ∂p.law.toMeasure = ∑' k, p.mass k • f k := by
  rw [integral_countable ((p.integrable_iff f).mpr hf)]
  simp only [p.law_real_singleton]


lemma CriticalEvenOffspring.integrable_id (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k : ℝ)) p.law.toMeasure := by
  apply (p.integrable_iff _).mpr
  simpa [Real.norm_natCast, mul_comm] using p.mean.summable


lemma CriticalEvenOffspring.integrable_sq (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k : ℝ)^2) p.law.toMeasure := by
  apply (p.integrable_iff _).mpr
  simpa [Real.norm_eq_abs, abs_sq, mul_comm] using p.second


lemma CriticalEvenOffspring.integral_id (p : CriticalEvenOffspring) :
    ∫ k : ℕ, (k : ℝ) ∂p.law.toMeasure = 1 := by
  rw [integral_countable p.integrable_id]
  simpa [mul_comm] using p.mean.tsum_eq


lemma CriticalEvenOffspring.integrable_step (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k : ℝ) - 1) p.law.toMeasure :=
  p.integrable_id.sub (integrable_const 1)


lemma CriticalEvenOffspring.integral_step (p : CriticalEvenOffspring) :
    ∫ k : ℕ, ((k : ℝ) - 1) ∂p.law.toMeasure = 0 := by
  rw [integral_sub p.integrable_id (integrable_const 1), p.integral_id]
  simp


lemma CriticalEvenOffspring.integrable_step_sq (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => ((k : ℝ) - 1)^2) p.law.toMeasure := by
  apply (p.integrable_iff _).mpr
  simpa [Real.norm_eq_abs, abs_sq, mul_comm] using p.summable_variance


lemma CriticalEvenOffspring.integral_step_sq (p : CriticalEvenOffspring) :
    ∫ k : ℕ, ((k : ℝ) - 1)^2 ∂p.law.toMeasure = p.variance := by
  rw [integral_countable p.integrable_step_sq]
  simp only [p.law_real_singleton, smul_eq_mul, variance, mul_comm]


def CriticalEvenOffspring.standardStep (p : CriticalEvenOffspring) (k : ℕ) : ℝ :=
  ((k : ℝ) - 1) / p.sigma


lemma CriticalEvenOffspring.integral_standardStep (p : CriticalEvenOffspring) :
    ∫ k, p.standardStep k ∂p.law.toMeasure = 0 := by
  simp [standardStep, integral_div, p.integral_step]


lemma CriticalEvenOffspring.integral_standardStep_sq (p : CriticalEvenOffspring) :
    ∫ k, p.standardStep k ^ 2 ∂p.law.toMeasure = 1 := by
  simp only [standardStep, div_pow, integral_div, p.integral_step_sq, sigma,
    Real.sq_sqrt p.variance_pos.le, div_self p.variance_pos.ne']


lemma CriticalEvenOffspring.charFun_power_limit (p : CriticalEvenOffspring) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      (charFun (p.law.toMeasure.map p.standardStep) ((Real.sqrt n)⁻¹ * t)) ^ n)
      atTop (𝓝 (Complex.exp (- (t : ℂ)^2 / 2))) := by
  exact tendsto_charFun_inv_sqrt_mul_pow
    (by fun_prop) p.integral_standardStep p.integral_standardStep_sq t


lemma CriticalEvenOffspring.charFun_gaussian_bound (p : CriticalEvenOffspring) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ Real.exp (-t^2/4) := by
  have ho := taylor_charFun_two (P := p.law.toMeasure) (X := p.standardStep)
    (by fun_prop) p.integral_standardStep p.integral_standardStep_sq
  have hb := ho.bound (by norm_num : (0 : ℝ) < 1/4)
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨min (r/2) 1, lt_min (by positivity) zero_lt_one, ?_⟩
  intro t ht
  have ht1 : |t| ≤ 1 := ht.trans (min_le_right _ _)
  have htr : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero]
    exact (ht.trans (min_le_left _ _)).trans_lt (by linarith)
  have hsq : t^2 ≤ 1 := (sq_le_one_iff_abs_le_one t).mpr ht1
  have he := hbound htr
  have hn : ‖(1 - (t : ℂ)^2 / 2)‖ = 1 - t^2/2 := by
    have heq : (1 - (t : ℂ)^2 / 2) = ((1 - t^2/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at he
  calc
    ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤
        ‖charFun (p.law.toMeasure.map p.standardStep) t - (1 - (t : ℂ)^2/2)‖ +
          ‖1 - (t : ℂ)^2/2‖ := by
      simpa only [add_comm] using (norm_le_insert'
        (charFun (p.law.toMeasure.map p.standardStep) t) (1 - (t : ℂ)^2/2))
    _ ≤ 1 - t^2/4 := by rw [hn]; linarith
    _ ≤ Real.exp (-t^2/4) := by
      linarith [Real.add_one_le_exp (-t^2/4)]


def CriticalEvenOffspring.iidLaw (p : CriticalEvenOffspring) (N : ℕ) :
    Measure (Fin N → ℕ) := Measure.pi (fun _ : Fin N => p.law.toMeasure)


instance (p : CriticalEvenOffspring) (N : ℕ) : IsProbabilityMeasure (p.iidLaw N) := by
  unfold CriticalEvenOffspring.iidLaw
  infer_instance


def totalStep {N : ℕ} (d : Fin N → ℕ) : ℤ := ∑ i, ((d i : ℤ) - 1)


lemma totalStep_eq_sum_sub {N : ℕ} (d : Fin N → ℕ) :
    totalStep d = (∑ i, d i : ℕ) - (N : ℤ) := by
  simp [totalStep, Finset.sum_sub_distrib]


lemma totalStep_measurable (N : ℕ) : Measurable (@totalStep N) := by
  unfold totalStep
  fun_prop


lemma CriticalEvenOffspring.ae_even (p : CriticalEvenOffspring) :
    ∀ᵐ k ∂p.law.toMeasure, Even k := by
  rw [ae_iff, p.law.toMeasure_apply_eq_zero_iff (by measurability), Set.disjoint_left]
  intro k hk hn
  have hzero : p.law k = 0 := by
    rw [p.law_apply, p.even_support k (Nat.not_even_iff_odd.mp hn), ENNReal.ofReal_zero]
  exact (p.law.mem_support_iff k).mp hk hzero


lemma CriticalEvenOffspring.iid_ae_even (p : CriticalEvenOffspring) (N : ℕ) :
    ∀ᵐ d ∂p.iidLaw N, ∀ i, Even (d i) := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin N => p.law.toMeasure) i).quasiMeasurePreserving.ae p.ae_even


lemma CriticalEvenOffspring.iid_totalStep_parity (p : CriticalEvenOffspring) (N : ℕ)
    {j : ℤ} (hj : Even ((N : ℤ) + j)) :
    ∀ᵐ d ∂p.iidLaw N, Even (totalStep d - j) := by
  filter_upwards [p.iid_ae_even N] with d hd
  rw [totalStep_eq_sum_sub, sub_sub]
  apply Even.sub _ hj
  exact_mod_cast Finset.even_sum d (fun i _ => hd i)


lemma CriticalEvenOffspring.iid_marginal_map (p : CriticalEvenOffspring) (N : ℕ)
    (i : Fin N) (f : ℕ → ℝ) :
    (p.iidLaw N).map (fun d => f (d i)) = p.law.toMeasure.map f := by
  have hf : Measurable f := measurable_of_countable f
  rw [← (measurePreserving_eval (fun _ : Fin N => p.law.toMeasure) i).map_eq,
    Measure.map_map hf (measurable_pi_apply i)]
  rfl


lemma CriticalEvenOffspring.charFun_step_scale (p : CriticalEvenOffspring) (t : ℝ) :
    charFun (p.law.toMeasure.map (fun k : ℕ => (k : ℝ) - 1)) t =
      charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t) := by
  rw [charFun_apply_real, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  congr 1
  ext k
  congr 2
  simp only [standardStep]
  push_cast
  field_simp [p.sigma_pos.ne']


lemma CriticalEvenOffspring.iid_charFun (p : CriticalEvenOffspring) (N : ℕ) (t : ℝ) :
    charFun ((p.iidLaw N).map (fun d => (totalStep d : ℝ))) t =
      (charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t))^N := by
  have heq : (fun d : Fin N → ℕ => (totalStep d : ℝ)) =
      fun d => ∑ i, ((d i : ℝ) - 1) := by
    ext d
    simp [totalStep]
  rw [heq]
  have hind : iIndepFun (fun i (d : Fin N → ℕ) => (d i : ℝ) - 1) (p.iidLaw N) :=
    iIndepFun_pi (μ := fun _ : Fin N => p.law.toMeasure)
      (X := fun _ k => (k : ℝ) - 1) (fun _ => by fun_prop)
  have hm (i : Fin N) : AEMeasurable (fun d : Fin N → ℕ => (d i : ℝ) - 1) (p.iidLaw N) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ) - 1)).comp
      (measurable_pi_apply i)).aemeasurable
  rw [congrFun (hind.charFun_map_fun_sum_eq_prod hm) t]
  simp only [Finset.prod_apply]
  simp_rw [p.iid_marginal_map N _ (fun k : ℕ => (k : ℝ) - 1), p.charFun_step_scale]
  simp


def CriticalEvenOffspring.streamLaw (p : CriticalEvenOffspring) : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => p.law.toMeasure)


instance (p : CriticalEvenOffspring) : IsProbabilityMeasure p.streamLaw := by
  unfold CriticalEvenOffspring.streamLaw
  infer_instance


def CriticalEvenOffspring.streamStep (p : CriticalEvenOffspring) (j : ℕ) (ω : ℕ → ℕ) : ℝ :=
  p.standardStep (ω j)


lemma CriticalEvenOffspring.standardStep_memLp (p : CriticalEvenOffspring) :
    MemLp p.standardStep 2 p.law.toMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [standardStep, div_pow] using p.integrable_step_sq.div_const (p.sigma^2)


lemma CriticalEvenOffspring.streamStep_memLp (p : CriticalEvenOffspring) (j : ℕ) :
    MemLp (p.streamStep j) 2 p.streamLaw :=
  p.standardStep_memLp.comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j)


lemma CriticalEvenOffspring.streamStep_indep (p : CriticalEvenOffspring) :
    iIndepFun p.streamStep p.streamLaw :=
  iIndepFun_infinitePi (fun _ => measurable_of_countable p.standardStep)


lemma CriticalEvenOffspring.streamStep_ident (p : CriticalEvenOffspring) (j : ℕ) :
    IdentDistrib (p.streamStep j) (p.streamStep 0) p.streamLaw p.streamLaw :=
  ((measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j).hasLaw.identDistrib
    (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) 0).hasLaw).comp
      (measurable_of_countable p.standardStep)


lemma CriticalEvenOffspring.streamStep_integral (p : CriticalEvenOffspring) (j : ℕ) :
    ∫ ω, p.streamStep j ω ∂p.streamLaw = 0 := by
  calc
    _ = ∫ k, p.standardStep k ∂p.law.toMeasure :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j).hasLaw.integral_comp
        (by fun_prop)
    _ = 0 := p.integral_standardStep


lemma CriticalEvenOffspring.streamStep_integral_sq (p : CriticalEvenOffspring) (j : ℕ) :
    ∫ ω, p.streamStep j ω ^ 2 ∂p.streamLaw = 1 := by
  calc
    _ = ∫ k, p.standardStep k ^ 2 ∂p.law.toMeasure :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j).hasLaw.integral_comp
        (by fun_prop)
    _ = 1 := p.integral_standardStep_sq


theorem CriticalEvenOffspring.streamWalk_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution (scaledWalk p.streamStep) atTop (brownianPath B)
      (fun _ => p.streamLaw) ν :=
  iid_scaledWalk_CLT p.streamStep (fun _ => by unfold streamStep; fun_prop)
    (p.streamStep_memLp 0) (p.streamStep_integral 0) (p.streamStep_integral_sq 0)
    p.streamStep_indep p.streamStep_ident hB


def CriticalEvenOffspring.iidWalk (p : CriticalEvenOffspring) (N : ℕ)
    (d : Fin N → ℕ) : C(unitInterval, ℝ) :=
  interpolation N (fun i =>
    (∑ j : Fin N, if j.val < i.val then p.standardStep (d j) else 0) / Real.sqrt N)


lemma CriticalEvenOffspring.iidWalk_measurable (p : CriticalEvenOffspring) (N : ℕ) :
    @Measurable (Fin N → ℕ) C(unitInterval, ℝ) _ (borel _) (p.iidWalk N) :=
  measurable_of_countable _


lemma CriticalEvenOffspring.stream_restrict_law (p : CriticalEvenOffspring) (N : ℕ) :
    HasLaw (fun ω : ℕ → ℕ => fun i : Fin N => ω i.val) (p.iidLaw N) p.streamLaw := by
  refine ⟨(Measurable.of_eval (fun index => measurable_pi_apply index.val)).aemeasurable, ?_⟩
  simpa only [streamLaw, iidLaw, Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => p.law.toMeasure)
      (@Fin.val_injective N))


lemma CriticalEvenOffspring.iidWalk_restrict (p : CriticalEvenOffspring) (N : ℕ) (ω : ℕ → ℕ) :
    p.iidWalk N (fun i => ω i.val) = scaledWalk p.streamStep N ω := by
  unfold iidWalk scaledWalk
  congr 1
  funext i
  congr 1
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro j hj
    have hjN : j < N := (Finset.mem_range.mp hj).trans_le (Nat.le_of_lt_succ i.isLt)
    exact ⟨⟨j,hjN⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩, rfl⟩
  · intro j hj
    rfl


theorem CriticalEvenOffspring.iidWalk_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution p.iidWalk atTop (brownianPath B) p.iidLaw ν := by
  refine ⟨fun n => (p.iidWalk_measurable n).aemeasurable,
    brownianPath_aemeasurable hB, ?_⟩
  have heq (N : ℕ) : (p.iidLaw N).map (p.iidWalk N) =
      p.streamLaw.map (scaledWalk p.streamStep N) := by
    rw [← (p.stream_restrict_law N).map_eq, Measure.map_map (p.iidWalk_measurable N)
      (Measurable.of_eval (fun index => measurable_pi_apply index.val))]
    congr 1
    funext ω
    exact p.iidWalk_restrict N ω
  simpa only [heq] using (p.streamWalk_CLT hB).tendsto


def iidSplit (m r : ℕ) : (Fin (m+r) → ℕ) ≃ᵐ ((Fin m → ℕ) × (Fin r → ℕ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m+r) => ℕ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => ℕ))


@[simp] lemma iidSplit_fst (m r : ℕ) (d : Fin (m+r) → ℕ) :
    (iidSplit m r d).1 = fun i => d (Fin.castAdd r i) := rfl


@[simp] lemma iidSplit_snd (m r : ℕ) (d : Fin (m+r) → ℕ) :
    (iidSplit m r d).2 = fun i => d (Fin.natAdd m i) := rfl


def stopTime (t : unitInterval) : C(unitInterval,unitInterval) where
  toFun s := min s t
  continuous_toFun := continuous_id.min continuous_const


def stopPath (t : unitInterval) (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ) :=
  f.comp (stopTime t)


lemma stopPath_apply (t s : unitInterval) (f : C(unitInterval,ℝ)) :
    stopPath t f s = f (min s t) := rfl


lemma stopPath_lipschitz (t : unitInterval) : LipschitzWith 1 (stopPath t) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le (dist_nonneg)).mpr
  intro s
  exact ContinuousMap.dist_apply_le_dist (min s t)


lemma continuous_stopPath (t : unitInterval) : Continuous (stopPath t) :=
  (stopPath_lipschitz t).continuous


lemma CriticalEvenOffspring.iidWalk_endpoint (p : CriticalEvenOffspring) {N : ℕ}
    (hN : 0 < N) (d : Fin N → ℕ) :
    p.iidWalk N d 1 = (totalStep d:ℝ)/(p.sigma*Real.sqrt N) := by
  have hg : gridPoint N (Fin.last N) = 1 := by
    apply Subtype.ext
    simp [gridPoint,hN.ne']
  unfold iidWalk
  rw [← hg,interpolation_gridPoint hN]
  simp only [Fin.val_last,Fin.is_lt,ite_true]
  simp_rw [standardStep]
  rw [← Finset.sum_div]
  have he : (∑ j : Fin N, ((d j:ℝ)-1)) = (totalStep d:ℝ) := by
    simp [totalStep]
  rw [he,div_div]


lemma CriticalEvenOffspring.iidWalk_agree_prefix (p : CriticalEvenOffspring)
    {N m : ℕ} {d e : Fin N → ℕ} {t : unitInterval}
    (ht : (N:ℝ)*(t:ℝ) ≤ m) (hde : ∀ j : Fin N, j.val < m → d j=e j) :
    stopPath t (p.iidWalk N d) = stopPath t (p.iidWalk N e) := by
  ext s
  change interpolation N _ (min s t) = interpolation N _ (min s t)
  rw [interpolation_apply,interpolation_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hz : hat N i.val (min s t)=0
  · simp only [hz,mul_zero]
  · have hi := hat_support hz
    have hist : ((min s t:unitInterval):ℝ) ≤ (t:ℝ) := by exact min_le_right s t
    have hi' : i.val ≤ m := by
      have hh : (i.val:ℝ) < (m:ℝ)+1 := by
        have hai := (abs_lt.mp hi).1
        have hmul := mul_le_mul_of_nonneg_left hist (Nat.cast_nonneg N (α := ℝ))
        linarith
      exact Nat.le_of_lt_succ (by exact_mod_cast hh)
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < i.val
    · rw [ite_eq_left hj,ite_eq_left hj,hde j (hj.trans_le hi')]
    · simp only [ite_eq_right hj]


def CriticalEvenOffspring.prefixWalk (p : CriticalEvenOffspring) (m r : ℕ)
    (t : unitInterval) (d : Fin m → ℕ) : C(unitInterval,ℝ) :=
  stopPath t (p.iidWalk (m+r) ((iidSplit m r).symm (d,fun _ => 1)))


lemma CriticalEvenOffspring.prefixWalk_eq (p : CriticalEvenOffspring) (m r : ℕ)
    {t : unitInterval} (ht : ((m+r:ℕ):ℝ)*(t:ℝ) ≤ m) (d : Fin (m+r) → ℕ) :
    p.prefixWalk m r t (iidSplit m r d).1 = stopPath t (p.iidWalk (m+r) d) := by
  apply p.iidWalk_agree_prefix ht
  intro j hj
  let i : Fin m := ⟨j.val,hj⟩
  have he : Fin.castAdd r i = j := Fin.ext rfl
  rw [← he]
  exact congrFun (congrArg Prod.fst ((iidSplit m r).apply_symm_apply
    ((iidSplit m r d).1,fun _ => 1))) i


lemma norm_tsum_smul_lt_one {α : Type*} [DecidableEq α]
    (w : α → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : HasSum w 1)
    (z : α → ℂ) (hz : ∀ k, ‖z k‖ = 1)
    {a b : α} (hab : a ≠ b) (ha : 0 < w a) (hb : 0 < w b)
    (hne : z a ≠ z b) : ‖∑' k, w k • z k‖ < 1 := by
  have hnorm : ∀ k, ‖w k • z k‖ = w k := by
    intro k
    rw [norm_smul, Real.norm_of_nonneg (hw k), hz, mul_one]
  have hsumNorm : Summable (fun k => ‖w k • z k‖) := by simpa only [hnorm] using hs.summable
  have hsum : Summable (fun k => w k • z k) := hsumNorm.of_norm
  have hstrict : ‖w a • z a + w b • z b‖ < w a + w b := by
    have hraw : ‖w a • z a + w b • z b‖ < ‖w a • z a‖ + ‖w b • z b‖ := by
      apply norm_add_lt_of_not_sameRay
      intro hr
      have he := hr.norm_smul_eq
      rw [hnorm a, hnorm b, smul_smul, smul_smul, mul_comm (w b) (w a)] at he
      exact hne ((smul_right_injective ℂ (mul_pos ha hb).ne' he).symm)
    simpa only [hnorm] using hraw
  have hdecomp := hsum.sum_add_tsum_compl (s := {a,b})
  have hwdecomp := hs.summable.sum_add_tsum_compl (s := {a,b})
  simp only [Finset.sum_pair hab] at hdecomp hwdecomp
  rw [hs.tsum_eq] at hwdecomp
  rw [← hdecomp]
  calc
    ‖w a • z a + w b • z b + ∑' k : {k : α // k ∉ ({a,b} : Finset α)}, w k.val • z k.val‖ ≤
        ‖w a • z a + w b • z b‖ +
          ‖∑' k : {k : α // k ∉ ({a,b} : Finset α)}, w k.val • z k.val‖ := norm_add_le _ _
    _ < w a + w b + ∑' k : {k : α // k ∉ ({a,b} : Finset α)}, w k.val := by
      apply add_lt_add_of_lt_of_le hstrict
      simpa only [hnorm] using norm_tsum_le_tsum_norm (hsumNorm.subtype _)
    _ = 1 := hwdecomp


lemma CriticalEvenOffspring.charFun_tsum (p : CriticalEvenOffspring) (t : ℝ) :
    charFun (p.law.toMeasure.map p.standardStep) t =
      ∑' k, p.mass k • Complex.exp ((t * p.standardStep k : ℝ) * Complex.I) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  simp only [← Complex.ofReal_mul]
  apply p.integral_eq_tsum
  simpa only [Complex.norm_exp_ofReal_mul_I, mul_one] using p.total.summable


lemma CriticalEvenOffspring.charFun_lt_one (p : CriticalEvenOffspring) {t : ℝ}
    (ht : t ≠ 0) (hbound : |t| ≤ p.sigma * Real.pi / 2) :
    ‖charFun (p.law.toMeasure.map p.standardStep) t‖ < 1 := by
  rw [p.charFun_tsum]
  apply norm_tsum_smul_lt_one p.mass p.nonneg p.total
    (fun k => Complex.exp ((t * p.standardStep k : ℝ) * Complex.I))
    (fun k => Complex.norm_exp_ofReal_mul_I _) (by norm_num : (0 : ℕ) ≠ 2)
    p.zero_pos p.two_pos
  intro he
  have hts : |t / p.sigma| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos p.sigma_pos, div_le_iff₀ p.sigma_pos]
    nlinarith [hbound]
  have hli : -Real.pi < -(t / p.sigma) := by
    have := (abs_le.mp hts).2
    linarith [Real.pi_pos]
  have hui : -(t / p.sigma) ≤ Real.pi := by
    have := (abs_le.mp hts).1
    linarith [Real.pi_pos]
  have hlj : -Real.pi < t / p.sigma := by
    have := (abs_le.mp hts).1
    linarith [Real.pi_pos]
  have huj : t / p.sigma ≤ Real.pi := by
    have := (abs_le.mp hts).2
    linarith [Real.pi_pos]
  have h0 : t * p.standardStep 0 = -(t / p.sigma) := by simp [standardStep, div_eq_mul_inv]
  have h2 : t * p.standardStep 2 = t / p.sigma := by norm_num [standardStep, div_eq_mul_inv]
  rw [h0, h2] at he
  have hx := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hli) (by simpa using hui)
    (by simpa using hlj) (by simpa using huj) he
  have hi := congrArg Complex.im hx
  simp only [Complex.mul_I_im, Complex.ofReal_re] at hi
  have hz : t / p.sigma = 0 := by linarith
  exact ht ((div_eq_zero_iff).mp hz |>.resolve_right p.sigma_pos.ne')


lemma CriticalEvenOffspring.charFun_compact_gap (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ t : ℝ,
      ε ≤ |t| → |t| ≤ p.sigma * Real.pi / 2 →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ ρ := by
  let K := {t : ℝ | ε ≤ |t| ∧ |t| ≤ p.sigma * Real.pi / 2}
  have hcompact : IsCompact K := by
    apply (isCompact_Icc (a := -(p.sigma * Real.pi / 2))
      (b := p.sigma * Real.pi / 2)).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · intro t ht
      exact abs_le.mp ht.2
  by_cases hne : K.Nonempty
  · obtain ⟨t, ht, hmax⟩ := hcompact.exists_isMaxOn hne
      ((continuous_charFun (μ := p.law.toMeasure.map p.standardStep)).norm.continuousOn)
    refine ⟨‖charFun (p.law.toMeasure.map p.standardStep) t‖, norm_nonneg _, ?_, ?_⟩
    · apply p.charFun_lt_one _ ht.2
      intro hz
      have := ht.1
      simp only [hz, abs_zero] at this
      linarith
    · intro u hu hu'
      exact hmax ⟨hu, hu'⟩
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro t ht ht'
    exact (hne ⟨t, ht, ht'⟩).elim


lemma CriticalEvenOffspring.charFun_global_gaussian (p : CriticalEvenOffspring) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |t| ≤ p.sigma * Real.pi / 2 →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ Real.exp (-c * t^2) := by
  obtain ⟨δ, hδ, hlocal⟩ := p.charFun_gaussian_bound
  obtain ⟨ρ, _, hρ, hgap⟩ := p.charFun_compact_gap hδ
  let a := p.sigma * Real.pi / 2
  have ha : 0 < a := div_pos (mul_pos p.sigma_pos Real.pi_pos) (by norm_num)
  let c := min (1/4 : ℝ) ((1-ρ)/a^2)
  have hc : 0 < c := lt_min (by norm_num) (div_pos (sub_pos.mpr hρ) (sq_pos_of_pos ha))
  refine ⟨c, hc, ?_⟩
  intro t ht
  by_cases hsmall : |t| ≤ δ
  · refine (hlocal t hsmall).trans (Real.exp_le_exp.mpr ?_)
    have := mul_le_mul_of_nonneg_right (min_le_left (1/4 : ℝ) ((1-ρ)/a^2)) (sq_nonneg t)
    change c * t^2 ≤ (1/4 : ℝ) * t^2 at this
    linarith
  · have hta : t^2 ≤ a^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) ha.le).mpr ht
    have hca : c * a^2 ≤ 1-ρ := by
      have h := min_le_right (1/4 : ℝ) ((1-ρ)/a^2)
      exact (le_div_iff₀ (sq_pos_of_pos ha)).mp h
    have hct := mul_le_mul_of_nonneg_left hta hc.le
    refine (hgap t (le_of_lt (lt_of_not_ge hsmall)) ht).trans ?_
    have hexp := Real.add_one_le_exp (-c*t^2)
    linarith


def CriticalEvenOffspring.fourierCutoff (p : CriticalEvenOffspring) (n : ℕ) (t : ℝ) : ℂ :=
  if |t| ≤ (p.sigma * Real.pi / 2) * Real.sqrt (n+1) then
    (charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1)))^(n+1)
  else 0


lemma CriticalEvenOffspring.cutoff_measurable (p : CriticalEvenOffspring) (n : ℕ) :
    Measurable (p.fourierCutoff n) := by
  apply Measurable.ite (measurableSet_le measurable_abs measurable_const)
  · exact ((continuous_charFun.comp (continuous_id.div_const _)).pow _).measurable
  · exact measurable_const


lemma CriticalEvenOffspring.cutoff_pointwise (p : CriticalEvenOffspring) (t : ℝ) :
    Tendsto (fun n => p.fourierCutoff n t) atTop
      (𝓝 (Complex.exp (-(t:ℂ)^2/2))) := by
  have ha : 0 < p.sigma * Real.pi / 2 := div_pos (mul_pos p.sigma_pos Real.pi_pos) (by norm_num)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n+1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hbound : ∀ᶠ n : ℕ in atTop, |t| ≤ (p.sigma * Real.pi / 2) * Real.sqrt (n+1) :=
    (hsqrt.const_mul_atTop ha).eventually_ge_atTop |t|
  have hp := (p.charFun_power_limit t).comp (tendsto_add_atTop_nat 1)
  apply hp.congr'
  filter_upwards [hbound] with n hn
  rw [fourierCutoff, ite_eq_left hn]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]


lemma CriticalEvenOffspring.cutoff_gaussian_bound (p : CriticalEvenOffspring)
    {c : ℝ} (hg : ∀ t : ℝ, |t| ≤ p.sigma * Real.pi / 2 →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ Real.exp (-c*t^2))
    (n : ℕ) (t : ℝ) : ‖p.fourierCutoff n t‖ ≤ Real.exp (-c*t^2) := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hs : 0 < Real.sqrt (n+1) := Real.sqrt_pos.mpr hn
  unfold fourierCutoff
  split_ifs with ht
  · rw [norm_pow]
    have hb : |t / Real.sqrt (n+1)| ≤ p.sigma * Real.pi / 2 := by
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      exact ht
    calc
      ‖charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1))‖^(n+1) ≤
          (Real.exp (-c*(t / Real.sqrt (n+1))^2))^(n+1) :=
        pow_le_pow_left₀ (norm_nonneg _) (hg _ hb) _
      _ = Real.exp (-c*t^2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [div_pow, Real.sq_sqrt hn.le, Nat.cast_add, Nat.cast_one]
        field_simp
  · simp only [norm_zero]
    exact (Real.exp_pos _).le


lemma CriticalEvenOffspring.cutoff_L1_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => ∫ t : ℝ,
      ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖)
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  let bound : ℝ → ℝ := fun t => Real.exp (-c*t^2) + Real.exp (-(1/2:ℝ)*t^2)
  have hnorm (t : ℝ) : ‖Complex.exp (-(t:ℂ)^2/2)‖ = Real.exp (-(1/2:ℝ)*t^2) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.div_ofNat]
    ring
  have hd := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n t => ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖)
    (f := fun _ => (0:ℝ)) bound
    (fun n => ((p.cutoff_measurable n).sub (by fun_prop)).norm.aestronglyMeasurable)
    ((integrable_exp_neg_mul_sq hc).add (integrable_exp_neg_mul_sq (by norm_num)))
    (fun n => ae_of_all _ fun t => ?_)
    (ae_of_all _ fun t => ?_)
  · simpa using hd
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (add_le_add (p.cutoff_gaussian_bound hg n t) (hnorm t).le)
  · exact tendsto_iff_norm_sub_tendsto_zero.mp (p.cutoff_pointwise t)


lemma integral_exp_even_int (k : ℤ) :
    (∫ t : ℝ in -(Real.pi / 2)..Real.pi / 2,
      Complex.exp ((2 * k : ℂ) * t * Complex.I)) =
        if k = 0 then (Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, ite_true,
      intervalIntegral.integral_const, sub_neg_eq_add, Complex.real_smul]
    push_cast
    ring
  · rw [ite_eq_right hk]
    have hc : (2 * k : ℂ) * Complex.I ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hk)) Complex.I_ne_zero
    simp_rw [mul_right_comm (2 * (k : ℂ)) _ Complex.I]
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp (((2 * k : ℂ) * Complex.I) * (Real.pi / 2 : ℝ)) =
        Complex.exp (((2 * k : ℂ) * Complex.I) * (-(Real.pi / 2) : ℝ)) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨k, ?_⟩
      push_cast
      ring
    rw [he, sub_self, zero_div]


lemma integral_exp_even_int' {k : ℤ} (hk : Even k) :
    (∫ t : ℝ in -(Real.pi / 2)..Real.pi / 2,
      Complex.exp ((k : ℂ) * t * Complex.I)) =
        if k = 0 then (Real.pi : ℂ) else 0 := by
  obtain ⟨r, rfl⟩ := hk
  convert integral_exp_even_int r using 1 <;> simp [two_mul]


lemma spanTwo_inversion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℤ) (hX : Measurable X)
    (j : ℤ) (hj : ∀ᵐ ω ∂P, Even (X ω - j)) :
    (∫ t : ℝ in -(Real.pi / 2)..Real.pi / 2,
      Complex.exp (-(j : ℂ) * t * Complex.I) *
        charFun (P.map (fun ω => (X ω : ℝ))) t) =
      (Real.pi : ℂ) * (P.real {ω | X ω = j} : ℂ) := by
  let f : ℝ → Ω → ℂ := fun t ω => Complex.exp (((X ω - j : ℤ) : ℂ) * t * Complex.I)
  have hmeas : Measurable (Function.uncurry f) := by
    dsimp [f, Function.uncurry]
    fun_prop
  let : IsFiniteMeasure (volume.restrict (uIoc (-(Real.pi/2)) (Real.pi/2))) :=
    ⟨by simp⟩
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc (-(Real.pi/2)) (Real.pi/2))).prod P) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      dsimp [f, Function.uncurry]
      have : ((X z.2 - j : ℤ) : ℂ) * z.1 = (((X z.2 - j : ℤ) : ℝ) * z.1 : ℝ) := by
        push_cast
        rfl
      rw [this, Complex.norm_exp_ofReal_mul_I]
  have hinner (t : ℝ) : Complex.exp (-(j : ℂ) * t * Complex.I) *
      charFun (P.map (fun ω => (X ω : ℝ))) t = ∫ ω, f t ω ∂P := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by
      dsimp [f]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  simp_rw [hinner]
  rw [intervalIntegral_integral_swap hint]
  have hcalc : (fun ω => ∫ t in -(Real.pi/2)..Real.pi/2, f t ω) =ᵐ[P]
      fun ω => if X ω = j then (Real.pi : ℂ) else 0 := by
    filter_upwards [hj] with ω hω
    dsimp [f]
    rw [integral_exp_even_int' hω]
    simp only [sub_eq_zero]
  rw [integral_congr_ae hcalc]
  have hm : MeasurableSet {ω | X ω = j} := hX (measurableSet_singleton j)
  have heq : (fun ω => if X ω = j then (Real.pi : ℂ) else 0) =
      {ω | X ω = j}.indicator (fun _ => (Real.pi : ℂ)) := by
    ext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator hm, integral_const]
  simp [Measure.real, Complex.real_smul, mul_comm]


def CriticalEvenOffspring.siteFourier (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) (t : ℝ) : ℂ :=
  p.fourierCutoff n t * Complex.exp ((-(j : ℝ) * t /
    (p.sigma * Real.sqrt (n+1)) : ℝ) * Complex.I)


lemma CriticalEvenOffspring.siteFourier_integral (p : CriticalEvenOffspring) (n : ℕ) (j : ℤ) :
    (∫ t : ℝ, p.siteFourier n j t) =
      (p.sigma * Real.sqrt (n+1)) •
        ∫ t : ℝ in -(Real.pi/2)..Real.pi/2,
          Complex.exp (-(j : ℂ) * t * Complex.I) *
            (charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t))^(n+1) := by
  let A := (p.sigma * Real.pi / 2) * Real.sqrt (n+1)
  let scale := p.sigma * Real.sqrt (n+1)
  let f : ℝ → ℂ := fun t =>
    (charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1)))^(n+1) *
      Complex.exp ((-(j : ℝ) * t / scale : ℝ) * Complex.I)
  have hsqrt : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : 0 < scale := mul_pos p.sigma_pos hsqrt
  have hA : 0 ≤ A := mul_nonneg
    (div_nonneg (mul_nonneg p.sigma_pos.le Real.pi_pos.le) (by norm_num)) hsqrt.le
  have heq : p.siteFourier n j = (Icc (-A) A).indicator f := by
    ext t
    simp only [siteFourier, fourierCutoff, Set.indicator_apply, mem_Icc, ← abs_le]
    split_ifs <;> simp [f, scale]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hA)]
  have hlo : -(Real.pi/2) * scale = -A := by dsimp [scale, A]; ring
  have hhi : (Real.pi/2) * scale = A := by dsimp [scale, A]; ring
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (a := -(Real.pi/2)) (b := Real.pi/2) f scale
  rw [hlo, hhi] at hsub
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f]
  have he : -(j : ℝ) * (t * scale) / scale = -(j : ℝ) * t := by
    field_simp
  have ht : t * scale / Real.sqrt (n+1) = p.sigma * t := by
    dsimp [scale]
    field_simp
  rw [he, ht]
  push_cast
  ring


lemma CriticalEvenOffspring.siteFourier_probability (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) (hj : Even (((n+1 : ℕ) : ℤ) + j)) :
    (∫ t : ℝ, p.siteFourier n j t) =
      (p.sigma * Real.sqrt (n+1) * Real.pi *
        (p.iidLaw (n+1)).real {d | totalStep d = j} : ℝ) := by
  have hi := spanTwo_inversion (p.iidLaw (n+1)) totalStep
    (totalStep_measurable _) j (p.iid_totalStep_parity _ hj)
  simp only [p.iid_charFun] at hi
  rw [p.siteFourier_integral, hi]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring


lemma CriticalEvenOffspring.iid_site_incompatible (p : CriticalEvenOffspring)
    (N : ℕ) (j : ℤ) (hj : ¬Even ((N : ℤ) + j)) :
    (p.iidLaw N).real {d | totalStep d = j} = 0 := by
  rw [measureReal_eq_zero_iff]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [p.iid_ae_even N] with d hd
  intro heq
  apply hj
  have heven : Even (∑ i, d i : ℕ) := Finset.even_sum d (fun i _ => hd i)
  have hcast : Even ((∑ i, d i : ℕ) : ℤ) := by exact_mod_cast heven
  have hs : (N : ℤ) + j = (∑ i, d i : ℕ) := by
    rw [totalStep_eq_sum_sub] at heq
    omega
  rwa [hs]


theorem CriticalEvenOffspring.iid_site_uniform_bound (p : CriticalEvenOffspring) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℤ),
      Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} ≤ C := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  have hs := p.sigma_pos
  refine ⟨Real.sqrt (Real.pi / c) / (p.sigma * Real.pi), by positivity, ?_⟩
  intro n j
  by_cases hj : Even (((n+1 : ℕ) : ℤ) + j)
  · have hnorm : ‖∫ t : ℝ, p.siteFourier n j t‖ ≤ Real.sqrt (Real.pi / c) := by
      have hbound : ∀ᵐ t ∂volume, ‖p.siteFourier n j t‖ ≤ Real.exp (-c*t^2) := by
        apply ae_of_all
        intro t
        simpa only [siteFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
          p.cutoff_gaussian_bound hg n t
      simpa only [integral_gaussian] using
        norm_integral_le_of_norm_le (integrable_exp_neg_mul_sq hc) hbound
    rw [p.siteFourier_probability n j hj, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)] at hnorm
    rw [le_div_iff₀ (mul_pos p.sigma_pos Real.pi_pos)]
    nlinarith
  · rw [p.iid_site_incompatible _ _ hj, mul_zero]
    positivity


lemma totalStep_succAbove {N : ℕ} (d : Fin (N+1) → ℕ) (i : Fin (N+1)) :
    totalStep d = (d i : ℤ) - 1 + totalStep (fun j => d (i.succAbove j)) := by
  exact Fin.sum_univ_succAbove (fun j => ((d j : ℤ) - 1)) i


lemma CriticalEvenOffspring.iid_coordinate_site (p : CriticalEvenOffspring)
    (N : ℕ) (i : Fin (N+1)) (k : ℕ) (j : ℤ) :
    (p.iidLaw (N+1)).real {d | d i = k ∧ totalStep d = j} =
      p.mass k * (p.iidLaw N).real {d | totalStep d = j - ((k : ℤ) - 1)} := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℕ) i
  have hp : MeasurePreserving e (p.iidLaw (N+1)) (p.law.toMeasure.prod (p.iidLaw N)) :=
    measurePreserving_piFinSuccAbove (fun _ => p.law.toMeasure) i
  have hset : {d : Fin (N+1) → ℕ | d i = k ∧ totalStep d = j} =
      e ⁻¹' (({k} : Set ℕ) ×ˢ {d : Fin N → ℕ | totalStep d = j - ((k : ℤ) - 1)}) := by
    ext d
    change (d i = k ∧ totalStep d = j) ↔
      (d i = k ∧ totalStep (fun a => d (i.succAbove a)) = j - ((k : ℤ) - 1))
    rw [totalStep_succAbove d i]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> refine ⟨h₁, ?_⟩ <;>
      rw [h₁] at * <;> omega
  rw [measureReal_def, hset, hp.measure_preimage (by measurability),
    Measure.prod_prod, ENNReal.toReal_mul, p.law_singleton,
    ENNReal.toReal_ofReal (p.nonneg _)]
  rfl


lemma CriticalEvenOffspring.law_real_set (p : CriticalEvenOffspring) (s : Set ℕ) :
    p.law.toMeasure.real s = ∑' k, s.indicator p.mass k := by
  classical
  rw [measureReal_def, p.law.toMeasure_apply (Set.to_countable s).measurableSet,
    ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro k
    by_cases hk : k ∈ s <;> simp [hk, p.nonneg]
  · intro k
    by_cases hk : k ∈ s <;> simp [hk]


lemma real_measure_coordinate_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℕ) (hf : Measurable f)
    (s : Set Ω) (hs : MeasurableSet s) :
    μ.real s = ∑' k : ℕ, μ.real {ω | f ω = k ∧ ω ∈ s} := by
  have hu : s = ⋃ k : ℕ, {ω | f ω = k ∧ ω ∈ s} := by ext ω; simp
  have hd : Pairwise (fun k l : ℕ => Disjoint {ω | f ω = k ∧ ω ∈ s}
      {ω | f ω = l ∧ ω ∈ s}) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro ω hω hω'
    exact hkl (hω.1.symm.trans hω'.1)
  conv_lhs => rw [measureReal_def, hu,
    measure_iUnion hd (fun k => (hf (measurableSet_singleton k)).inter hs),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  rfl


lemma CriticalEvenOffspring.iid_coordinate_tail_sum (p : CriticalEvenOffspring)
    (N : ℕ) (i : Fin (N+1)) (R : ℝ) (j : ℤ) :
    (p.iidLaw (N+1)).real {d | R < (d i : ℝ) ∧ totalStep d = j} =
      ∑' k : ℕ, if R < (k : ℝ) then p.mass k *
        (p.iidLaw N).real {d | totalStep d = j - ((k : ℤ) - 1)} else 0 := by
  rw [real_measure_coordinate_decomposition _ (fun d => d i) (measurable_pi_apply i) _
    (by measurability)]
  simp only [Set.mem_ofPred_eq]
  apply tsum_congr
  intro k
  by_cases hk : R < (k : ℝ)
  · rw [ite_eq_left hk]
    have hs : {d : Fin (N+1) → ℕ | d i = k ∧ R < (d i : ℝ) ∧ totalStep d = j} =
        {d | d i = k ∧ totalStep d = j} := by
      ext d
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₁.symm ▸ hk, h₂⟩
    rw [hs, p.iid_coordinate_site]
  · rw [ite_eq_right hk]
    have hs : {d : Fin (N+1) → ℕ | d i = k ∧ R < (d i : ℝ) ∧ totalStep d = j} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h₁ h₂ _
      exact hk (h₁ ▸ h₂)
    rw [hs, measureReal_empty]


lemma CriticalEvenOffspring.iid_coordinate_tail_bound (p : CriticalEvenOffspring)
    {C : ℝ} (hC : ∀ (n : ℕ) (j : ℤ),
      Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} ≤ C)
    (n : ℕ) (i : Fin (n+2)) (R : ℝ) (j : ℤ) :
    Real.sqrt (n+1) * (p.iidLaw (n+2)).real
        {d | R < (d i : ℝ) ∧ totalStep d = j} ≤
      C * p.law.toMeasure.real {k | R < (k : ℝ)} := by
  rw [p.iid_coordinate_tail_sum (n+1) i R j, p.law_real_set, ← tsum_mul_left, ← tsum_mul_left]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hmass : Summable (fun k : ℕ => if R < (k : ℝ) then p.mass k else 0) :=
    p.total.summable.of_nonneg_of_le
      (fun k => by split_ifs <;> simp [p.nonneg])
      (fun k => by split_ifs <;> simp [p.nonneg])
  have hm : Summable (fun k : ℕ => if R < (k : ℝ) then p.mass k *
      (p.iidLaw (n+1)).real {d | totalStep d = j - ((k : ℤ) - 1)} else 0) := by
    apply p.total.summable.of_nonneg_of_le
    · intro k
      split_ifs
      · exact mul_nonneg (p.nonneg _) measureReal_nonneg
      · rfl
    · intro k
      split_ifs
      · exact mul_le_of_le_one_right (p.nonneg _) measureReal_le_one
      · exact p.nonneg _
  apply Summable.tsum_le_tsum _ (hm.mul_left _) (hmass.mul_left _)
  intro k
  split_ifs
  · have h := mul_le_mul_of_nonneg_left (hC n (j - ((k : ℤ) - 1))) (p.nonneg k)
    nlinarith
  · simp


lemma CriticalEvenOffspring.iid_max_tail_bound (p : CriticalEvenOffspring)
    {C : ℝ} (hC : ∀ (n : ℕ) (j : ℤ),
      Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} ≤ C)
    (n : ℕ) (R : ℝ) (j : ℤ) :
    Real.sqrt (n+1) * (p.iidLaw (n+2)).real
        {d | (∃ i, R < (d i : ℝ)) ∧ totalStep d = j} ≤
      (n+2 : ℝ) * C * p.law.toMeasure.real {k | R < (k : ℝ)} := by
  have hu : {d : Fin (n+2) → ℕ | (∃ i, R < (d i : ℝ)) ∧ totalStep d = j} =
      ⋃ i : Fin (n+2), {d | R < (d i : ℝ) ∧ totalStep d = j} := by
    ext d
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    aesop
  rw [hu]
  calc
    _ ≤ Real.sqrt (n+1) * ∑ i : Fin (n+2), (p.iidLaw (n+2)).real
        {d | R < (d i : ℝ) ∧ totalStep d = j} :=
      mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le _) (Real.sqrt_nonneg _)
    _ ≤ ∑ _i : Fin (n+2), C * p.law.toMeasure.real {k | R < (k : ℝ)} := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact p.iid_coordinate_tail_bound hC n i R j
    _ = _ := by simp [Nat.cast_add, Nat.cast_ofNat, mul_assoc]


lemma gaussian_fourier_shift (x : ℝ) :
    (∫ t : ℝ, Complex.exp (-(t:ℂ)^2/2) *
      Complex.exp ((-x*t : ℝ) * Complex.I)) =
      (Real.sqrt (2*Real.pi) * Real.exp (-x^2/2) : ℝ) := by
  have h := fourierIntegral_gaussian (b := (1/2:ℂ)) (by norm_num) (-(x:ℂ))
  have hpow : (Real.pi / (1/2:ℂ)) ^ (1/2:ℂ) = (Real.sqrt (2*Real.pi) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    ring
  rw [hpow] at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with t
    rw [mul_comm]
    congr 2 <;> push_cast <;> ring
  · push_cast
    congr 2
    ring


lemma gaussian_phase_integrable (x : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-(t:ℂ)^2/2) *
      Complex.exp ((-x*t : ℝ) * Complex.I)) := by
  apply (integrable_exp_neg_mul_sq (show (0:ℝ)<1/2 by norm_num)).mono' (by fun_prop)
  filter_upwards [] with t
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp]
  apply le_of_eq
  congr 1
  simp only [Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.div_ofNat]
  ring


lemma CriticalEvenOffspring.siteFourier_integrable (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) : Integrable (p.siteFourier n j) := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  apply (integrable_exp_neg_mul_sq hc).mono' ?_ ?_
  · exact ((p.cutoff_measurable n).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with t
    simpa only [siteFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
      p.cutoff_gaussian_bound hg n t


def CriticalEvenOffspring.localCLTError (p : CriticalEvenOffspring) (n : ℕ) : ℝ :=
  ∫ t : ℝ, ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖


lemma CriticalEvenOffspring.siteFourier_gaussian_error (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) :
    ‖(∫ t : ℝ, p.siteFourier n j t) -
      (Real.sqrt (2*Real.pi) * Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2) : ℝ)‖ ≤
      p.localCLTError n := by
  let x : ℝ := (j:ℝ)/(p.sigma*Real.sqrt (n+1))
  have heq (t : ℝ) : -(j:ℝ)*t/(p.sigma*Real.sqrt (n+1)) = -x*t := by
    dsimp [x]
    ring
  change ‖(∫ t : ℝ, p.siteFourier n j t) -
    (Real.sqrt (2*Real.pi) * Real.exp (-x^2/2) : ℝ)‖ ≤ _
  rw [← gaussian_fourier_shift x, ← integral_sub (p.siteFourier_integrable n j)
    (gaussian_phase_integrable x)]
  have hn (t : ℝ) : ‖p.siteFourier n j t -
      Complex.exp (-(t:ℂ)^2/2) * Complex.exp ((-x*t:ℝ)*Complex.I)‖ =
      ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖ := by
    rw [siteFourier, heq, ← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  calc
    _ ≤ ∫ t : ℝ, ‖p.siteFourier n j t -
      Complex.exp (-(t:ℂ)^2/2) * Complex.exp ((-x*t:ℝ)*Complex.I)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp only [hn, localCLTError]


theorem CriticalEvenOffspring.uniform_local_limit (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (n : ℕ) (j : ℤ), Even (((n+1:ℕ):ℤ)+j) →
        |Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} -
          (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2)| ≤ E n := by
  refine ⟨fun n => p.localCLTError n / (p.sigma*Real.pi), fun n => ?_, ?_, ?_⟩
  · exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _))
      (mul_pos p.sigma_pos Real.pi_pos).le
  · simpa only [zero_div, localCLTError] using p.cutoff_L1_limit.div_const (p.sigma*Real.pi)
  · intro n j hj
    have h := p.siteFourier_gaussian_error n j
    rw [p.siteFourier_probability n j hj, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    have hs : 0 < p.sigma*Real.pi := mul_pos p.sigma_pos Real.pi_pos
    have heq :
        (Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} -
          (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2)) * (p.sigma*Real.pi) =
        p.sigma * Real.sqrt (n+1) * Real.pi * (p.iidLaw (n+1)).real {d | totalStep d = j} -
          Real.sqrt (2*Real.pi) * Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2) := by
      field_simp [p.sigma_pos.ne']
    rw [← heq, abs_mul, abs_of_pos hs] at h
    exact (le_div_iff₀ hs).2 h


lemma gaussianProfile_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y^2/2)) (-x*Real.exp (-x^2/2)) x := by
  convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp) using 1 <;>
    simp only [id_eq, Pi.neg_apply, Pi.pow_apply]
  ring


lemma gaussianProfile_deriv_bound (x : ℝ) : |(-x)*Real.exp (-x^2/2)| ≤ 1 := by
  have hx : |x| ≤ Real.exp (x^2/2) := by
    have he := Real.add_one_le_exp (x^2/2)
    have hs := sq_nonneg (|x|-1)
    nlinarith [sq_abs x]
  have heq : -x^2/2 = -(x^2/2) := by ring
  rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _), heq, Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos _)).mpr hx


lemma gaussianProfile_lipschitz : LipschitzWith 1 (fun x : ℝ => Real.exp (-x^2/2)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (gaussianProfile_hasDerivAt x).differentiableAt)
  intro x
  rw [(gaussianProfile_hasDerivAt x).deriv]
  exact_mod_cast gaussianProfile_deriv_bound x


lemma gaussianProfile_sub_bound (x y : ℝ) :
    |Real.exp (-x^2/2)-Real.exp (-y^2/2)| ≤ |x-y| := by
  simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using gaussianProfile_lipschitz.dist_le_mul x y


theorem CriticalEvenOffspring.local_limit_oscillation (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (n : ℕ) (j k : ℤ), Even (((n+1:ℕ):ℤ)+j) → Even (((n+1:ℕ):ℤ)+k) →
        |Real.sqrt (n+1) * ((p.iidLaw (n+1)).real {d | totalStep d = j} -
          (p.iidLaw (n+1)).real {d | totalStep d = k})| ≤
        2*E n + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          |(j:ℝ)-(k:ℝ)| /(p.sigma*Real.sqrt (n+1)) := by
  obtain ⟨E,hE,hEt,hbound⟩ := p.uniform_local_limit
  refine ⟨E,hE,hEt,?_⟩
  intro n j k hj hk
  let a := p.sigma*Real.sqrt (n+1)
  let b := Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)
  have ha : 0 < a := mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity))
  have hb : 0 ≤ b := div_nonneg (by positivity) (mul_pos p.sigma_pos Real.pi_pos).le
  have hg : |b*Real.exp (-((j:ℝ)/a)^2/2)-b*Real.exp (-((k:ℝ)/a)^2/2)| ≤
      b*|(j:ℝ)-(k:ℝ)| /a := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hb]
    have h := mul_le_mul_of_nonneg_left (gaussianProfile_sub_bound ((j:ℝ)/a) ((k:ℝ)/a)) hb
    rw [← sub_div,abs_div,abs_of_pos ha] at h
    simpa only [mul_div_assoc] using h
  have hj' := hbound n j hj
  have hk' := hbound n k hk
  have ht₁ := abs_sub_le (Real.sqrt (n+1)*(p.iidLaw (n+1)).real {d | totalStep d = j})
    (b*Real.exp (-((j:ℝ)/a)^2/2))
    (Real.sqrt (n+1)*(p.iidLaw (n+1)).real {d | totalStep d = k})
  have ht₂ := abs_sub_le (b*Real.exp (-((j:ℝ)/a)^2/2))
    (b*Real.exp (-((k:ℝ)/a)^2/2))
    (Real.sqrt (n+1)*(p.iidLaw (n+1)).real {d | totalStep d = k})
  rw [abs_sub_comm (b*Real.exp (-((k:ℝ)/a)^2/2))] at ht₂
  rw [mul_sub]
  change _ ≤ 2*E n + b*|(j:ℝ)-(k:ℝ)| /a
  change |_ - b*Real.exp (-((j:ℝ)/a)^2/2)| ≤ E n at hj'
  change |_ - b*Real.exp (-((k:ℝ)/a)^2/2)| ≤ E n at hk'
  linarith


theorem CriticalEvenOffspring.suffix_site_oscillation (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (m r : ℕ) (j k : ℤ), Even (((m+(r+1):ℕ):ℤ)+j) →
        Even (((m+(r+1):ℕ):ℤ)+k) →
        ∀ᵐ d ∂p.iidLaw m,
          |(p.iidLaw (r+1)).real {b | totalStep b=j-totalStep d} -
            (p.iidLaw (r+1)).real {b | totalStep b=k-totalStep d}| ≤
          (2*E r + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
            |(j:ℝ)-(k:ℝ)| /(p.sigma*Real.sqrt (r+1))) / Real.sqrt (r+1) := by
  obtain ⟨E,hE,hEt,hb⟩ := p.local_limit_oscillation
  refine ⟨E,hE,hEt,?_⟩
  intro m r j k hj hk
  filter_upwards [p.iid_ae_even m] with d hd
  have hp : Even ((m:ℤ)+totalStep d) := by
    rw [totalStep_eq_sum_sub]
    have he : (m:ℤ)+((∑ i, d i : ℕ):ℤ)-(m:ℤ) = ((∑ i, d i : ℕ):ℤ) := by ring
    rw [← add_sub_assoc,he]
    exact_mod_cast Finset.even_sum d (fun i _ => hd i)
  have hj' : Even (((r+1:ℕ):ℤ)+(j-totalStep d)) := by
    have he : (((r+1:ℕ):ℤ)+(j-totalStep d)) =
        (((m+(r+1):ℕ):ℤ)+j)-((m:ℤ)+totalStep d) := by push_cast; ring
    rw [he]
    exact hj.sub hp
  have hk' : Even (((r+1:ℕ):ℤ)+(k-totalStep d)) := by
    have he : (((r+1:ℕ):ℤ)+(k-totalStep d)) =
        (((m+(r+1):ℕ):ℤ)+k)-((m:ℤ)+totalStep d) := by push_cast; ring
    rw [he]
    exact hk.sub hp
  have h := hb r (j-totalStep d) (k-totalStep d) hj' hk'
  have hs : 0 < Real.sqrt (r+1) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_mul,abs_of_pos hs] at h
  have he : ((j-totalStep d:ℤ):ℝ)-((k-totalStep d:ℤ):ℝ) = (j:ℝ)-(k:ℝ) := by
    push_cast
    ring
  rw [he] at h
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using h)


lemma totalStep_split (m r : ℕ) (d : Fin (m+r) → ℕ) :
    totalStep d = totalStep (iidSplit m r d).1 + totalStep (iidSplit m r d).2 := by
  exact Fin.sum_univ_add _


lemma iidSplit_preserving (μ : Measure ℕ) [SigmaFinite μ] (m r : ℕ) :
    MeasurePreserving (iidSplit m r) (Measure.pi (fun _ : Fin (m+r) => μ))
      ((Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi (fun _ : Fin r => μ))) := by
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (m+r) => μ) finSumFinEquiv).symm


lemma iid_prefix_test_endpoint (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j : ℤ) (F : (Fin m → ℕ) → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hF : ∀ d, |F d| ≤ M) :
    (∫ d, (if totalStep d = j then F (iidSplit m r d).1 else 0)
      ∂(Measure.pi (fun _ : Fin (m+r) => μ))) =
    ∫ a, F a * (Measure.pi (fun _ : Fin r => μ)).real
      {b | totalStep b = j-totalStep a} ∂(Measure.pi (fun _ : Fin m => μ)) := by
  let f : ((Fin m → ℕ) × (Fin r → ℕ)) → ℝ := fun x =>
    if totalStep x.1 + totalStep x.2 = j then F x.1 else 0
  have hf : Integrable f ((Measure.pi (fun _ : Fin m => μ)).prod
      (Measure.pi (fun _ : Fin r => μ))) := by
    apply (integrable_const M).mono' (by measurability)
    filter_upwards [] with x
    dsimp [f]
    split
    · exact hF _
    · simpa only [abs_zero] using hM
  have heq : (fun d => if totalStep d = j then F (iidSplit m r d).1 else 0) =
      f ∘ iidSplit m r := by
    funext d
    simp only [Function.comp_apply,f,totalStep_split]
  rw [heq]
  change (∫ d, f (iidSplit m r d) ∂(Measure.pi (fun _ : Fin (m+r) => μ))) = _
  rw [(iidSplit_preserving μ m r).integral_comp' f,integral_prod f hf]
  apply integral_congr_ae
  filter_upwards [] with a
  have hi : (fun b => f (a,b)) =
      ({b | totalStep b = j-totalStep a} : Set (Fin r → ℕ)).indicator (fun _ => F a) := by
    funext b
    simp only [f, Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [show (totalStep a + totalStep b = j) ↔
      (totalStep b = j-totalStep a) by omega]
  rw [hi, integral_indicator (by measurability),setIntegral_const]
  simp only [smul_eq_mul, mul_comm]


lemma integral_cond_eq_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (hE : MeasurableSet E) (F : Ω → ℝ) :
    (∫ ω, F ω ∂cond μ E) = (∫ ω, E.indicator F ω ∂μ)/μ.real E := by
  rw [ProbabilityTheory.cond,integral_smul_measure,integral_indicator hE,ENNReal.toReal_inv]
  simp only [smul_eq_mul,measureReal_def,div_eq_mul_inv,mul_comm]


def endpointWindow (s : Finset ℤ) (w : ℤ → ℝ) (z : ℤ) : ℝ :=
  ∑ j ∈ s, if z=j then w j else 0


lemma endpointWindow_apply (s : Finset ℤ) (w : ℤ → ℝ) (z : ℤ) :
    endpointWindow s w z = if z ∈ s then w z else 0 := by
  classical
  simp [endpointWindow]


lemma iid_prefix_test_window (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (s : Finset ℤ) (w : ℤ → ℝ) (F : (Fin m → ℕ) → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hF : ∀ d, |F d| ≤ M) :
    (∫ d, F (iidSplit m r d).1 * endpointWindow s w (totalStep d)
      ∂(Measure.pi (fun _ : Fin (m+r) => μ))) =
    ∫ a, F a * (∑ j ∈ s, w j * (Measure.pi (fun _ : Fin r => μ)).real
      {b | totalStep b = j-totalStep a}) ∂(Measure.pi (fun _ : Fin m => μ)) := by
  classical
  have hif (j : ℤ) : Integrable (fun d : Fin (m+r) → ℕ =>
      if totalStep d=j then F (iidSplit m r d).1 else 0)
      (Measure.pi (fun _ : Fin (m+r) => μ)) := by
    apply (integrable_const M).mono' (by measurability)
    filter_upwards [] with d
    split
    · exact hF _
    · simpa using hM
  have hsite (j : ℤ) : Integrable (fun a : Fin m → ℕ =>
      F a*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a})
      (Measure.pi (fun _ : Fin m => μ)) := by
    apply (integrable_const M).mono' (by measurability)
    filter_upwards [] with a
    change |F a*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}| ≤ M
    rw [abs_mul,abs_of_nonneg measureReal_nonneg]
    exact (mul_le_mul_of_nonneg_right (hF a) measureReal_nonneg).trans
      (mul_le_of_le_one_right hM (measureReal_le_one))
  have he (d : Fin (m+r) → ℕ) :
      F (iidSplit m r d).1 * endpointWindow s w (totalStep d) =
      ∑ j ∈ s, w j*(if totalStep d=j then F (iidSplit m r d).1 else 0) := by
    rw [endpointWindow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> ring
  have he' (a : Fin m → ℕ) :
      F a * (∑ j ∈ s, w j*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}) =
      ∑ j ∈ s, w j*(F a*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he,he']
  rw [integral_finsetSum s (fun j _ => (hif j).const_mul (w j)),
    integral_finsetSum s (fun j _ => (hsite j).const_mul (w j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_const_mul,iid_prefix_test_endpoint μ m r j F hM hF]


lemma normalized_integral_stability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k l F : Ω → ℝ} {M a : ℝ}
    (hk : Integrable k μ) (hl : Integrable l μ)
    (hl0 : ∀ᵐ ω ∂μ, 0 ≤ l ω)
    (hK : 0 < ∫ ω, k ω ∂μ) (hL : 0 < ∫ ω, l ω ∂μ)
    (hF : AEStronglyMeasurable F μ) (hM : 0 ≤ M)
    (hFM : ∀ᵐ ω ∂μ, |F ω| ≤ M)
    (ha : ∫ ω, |k ω-l ω| ∂μ ≤ a) :
    |(∫ ω, F ω*k ω ∂μ)/(∫ ω, k ω ∂μ) -
      (∫ ω, F ω*l ω ∂μ)/(∫ ω, l ω ∂μ)| ≤
      2*M*a/(∫ ω, k ω ∂μ) := by
  have hFk : Integrable (fun ω => F ω*k ω) μ :=
    (hk.norm.const_mul M).mono' (hF.mul hk.aestronglyMeasurable) (by
      filter_upwards [hFM] with ω hω
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hω (abs_nonneg (k ω)))
  have hFl : Integrable (fun ω => F ω*l ω) μ :=
    (hl.norm.const_mul M).mono' (hF.mul hl.aestronglyMeasurable) (by
      filter_upwards [hFM] with ω hω
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hω (abs_nonneg (l ω)))
  let K := ∫ ω, k ω ∂μ
  let L := ∫ ω, l ω ∂μ
  let A := ∫ ω, F ω*k ω ∂μ
  let D := ∫ ω, F ω*l ω ∂μ
  have hAD : |A-D| ≤ M*a := by
    rw [show A-D = ∫ ω, F ω*(k ω-l ω) ∂μ by
      simp only [A,D,mul_sub,integral_sub hFk hFl]]
    calc
      _ ≤ ∫ ω, |F ω*(k ω-l ω)| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun ω => F ω*(k ω-l ω))
      _ ≤ ∫ ω, M*|k ω-l ω| ∂μ := by
        apply integral_mono_ae
        · simpa only [mul_sub, Pi.sub_apply, Real.norm_eq_abs] using (hFk.sub hFl).norm
        · exact (hk.sub hl).norm.const_mul M
        · filter_upwards [hFM] with ω hω
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
      _ ≤ M*a := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left ha hM
  have hKL : |L-K| ≤ a := by
    calc
      _ = |∫ ω, k ω-l ω ∂μ| := by rw [integral_sub hk hl]; exact abs_sub_comm _ _
      _ ≤ ∫ ω, |k ω-l ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => k ω-l ω)
      _ ≤ a := ha
  have hD : |D| ≤ M*L := by
    calc
      _ ≤ ∫ ω, |F ω*l ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => F ω*l ω)
      _ ≤ ∫ ω, M*l ω ∂μ := by
        apply integral_mono_ae hFl.norm (hl.const_mul M)
        filter_upwards [hFM,hl0] with ω hω hlω
        change |F ω*l ω| ≤ M*l ω
        rw [abs_mul,abs_of_nonneg hlω]
        exact mul_le_mul_of_nonneg_right hω hlω
      _ = M*L := integral_const_mul _ _
  have hA0 : 0 ≤ a := (integral_nonneg (fun _ => abs_nonneg _)).trans ha
  have hK' : K ≠ 0 := hK.ne'
  have hL' : L ≠ 0 := hL.ne'
  have he : A/K-D/L = (A-D)/K + D*(L-K)/(K*L) := by
    field_simp [hK',hL']
    ring
  change |A/K-D/L| ≤ 2*M*a/K
  rw [he]
  calc
    _ ≤ |(A-D)/K| + |D*(L-K)/(K*L)| := abs_add_le _ _
    _ = |A-D|/K + |D| *|L-K|/(K*L) := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hK,abs_of_pos (mul_pos hK hL)]
    _ ≤ (M*a)/K + (M*L)*a/(K*L) := by
      exact add_le_add (div_le_div_of_nonneg_right hAD hK.le)
        (div_le_div_of_nonneg_right (mul_le_mul hD hKL (abs_nonneg _) (by positivity))
          (mul_pos hK hL).le)
    _ = _ := by field_simp [hK',hL']; ring


lemma finite_window_stability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (k : ι → Ω → ℝ) (k₀ F : Ω → ℝ) {M a : ℝ}
    (hw : ∀ j ∈ s, 0 ≤ w j) (hW : 0 < ∑ j ∈ s, w j)
    (hk : ∀ j ∈ s, Integrable (k j) μ) (hk₀ : Integrable k₀ μ)
    (hk0 : ∀ j ∈ s, ∀ᵐ ω ∂μ, 0 ≤ k j ω)
    (hK : 0 < ∫ ω, k₀ ω ∂μ)
    (hL : 0 < ∫ ω, (∑ j ∈ s, w j*k j ω) ∂μ)
    (hF : AEStronglyMeasurable F μ) (hM : 0 ≤ M)
    (hFM : ∀ᵐ ω ∂μ, |F ω| ≤ M)
    (hd : ∀ j ∈ s, ∀ᵐ ω ∂μ, |k₀ ω-k j ω| ≤ a) :
    |(∫ ω, F ω*k₀ ω ∂μ)/(∫ ω, k₀ ω ∂μ) -
      (∫ ω, F ω*(∑ j ∈ s, w j*k j ω) ∂μ)/
        (∫ ω, (∑ j ∈ s, w j*k j ω) ∂μ)| ≤ 2*M*a/(∫ ω, k₀ ω ∂μ) := by
  classical
  let W := ∑ j ∈ s, w j
  let l : Ω → ℝ := fun ω => (∑ j ∈ s, w j*k j ω)/W
  have hl' : Integrable (fun ω => ∑ j ∈ s, w j*k j ω) μ :=
    integrable_finsetSum s (fun j hj => (hk j hj).const_mul (w j))
  have hl : Integrable l μ := hl'.div_const W
  have hl0 : ∀ᵐ ω ∂μ, 0 ≤ l ω := by
    filter_upwards [(s.eventually_all).mpr hk0] with ω hω
    exact div_nonneg (Finset.sum_nonneg (fun j hj => mul_nonneg (hw j hj) (hω j hj))) hW.le
  have hLp : 0 < ∫ ω, l ω ∂μ := by
    dsimp [l]
    rw [integral_div]
    exact div_pos hL hW
  have hdiff : ∀ᵐ ω ∂μ, |k₀ ω-l ω| ≤ a := by
    filter_upwards [(s.eventually_all).mpr hd] with ω hω
    have he : k₀ ω-l ω = (∑ j ∈ s, w j*(k₀ ω-k j ω))/W := by
      dsimp [l]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      dsimp [W]
      field_simp [hW.ne']
    rw [he,abs_div,abs_of_pos hW]
    apply (div_le_iff₀ hW).mpr
    calc
      _ ≤ ∑ j ∈ s, |w j*(k₀ ω-k j ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, w j*a := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul,abs_of_nonneg (hw j hj)]
        exact mul_le_mul_of_nonneg_left (hω j hj) (hw j hj)
      _ = a*W := by rw [← Finset.sum_mul,mul_comm]
  have ha : ∫ ω, |k₀ ω-l ω| ∂μ ≤ a := by
    calc
      _ ≤ ∫ _, a ∂μ := integral_mono_ae (hk₀.sub hl).norm (integrable_const a) (by
        filter_upwards [hdiff] with ω hω
        exact hω)
      _ = a := by simp
  have h := normalized_integral_stability hk₀ hl hl0 hK hLp hF hM hFM ha
  have he : (∫ ω, F ω*l ω ∂μ)/(∫ ω, l ω ∂μ) =
      (∫ ω, F ω*(∑ j ∈ s, w j*k j ω) ∂μ)/
        (∫ ω, (∑ j ∈ s, w j*k j ω) ∂μ) := by
    have hn : (∫ ω, F ω*l ω ∂μ) =
        (∫ ω, F ω*(∑ j ∈ s, w j*k j ω) ∂μ)/W := by
      simp_rw [l, ← mul_div_assoc, integral_div]
    rw [hn]
    dsimp [l]
    rw [integral_div]
    exact div_div_div_cancel_right₀ hW.ne' _ _
  rw [he] at h
  exact h


lemma iid_site_convolution (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j : ℤ) :
    (Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j} =
      ∫ a, (Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}
        ∂(Measure.pi (fun _ : Fin m => μ)) := by
  have h := iid_prefix_test_endpoint μ m r j (fun _ => 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun _ => by norm_num)
  simp only [one_mul] at h
  rw [show (fun d : Fin (m+r) → ℕ => if totalStep d=j then (1:ℝ) else 0) =
      ({d | totalStep d=j} : Set (Fin (m+r) → ℕ)).indicator (fun _ => 1) by funext d; simp [Set.indicator_apply],
    integral_indicator (by measurability),setIntegral_const] at h
  simpa only [smul_eq_mul,mul_one] using h


theorem iid_prefix_window_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j₀ : ℤ) (s : Finset ℤ) (w : ℤ → ℝ)
    (hj₀ : j₀ ∈ s) (hw : ∀ j ∈ s, 0 ≤ w j) (hw₀ : 0 < w j₀)
    (hP : 0 < (Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j₀})
    (F : (Fin m → ℕ) → ℝ) {M a : ℝ} (hM : 0 ≤ M) (hF : ∀ d, |F d| ≤ M)
    (hd : ∀ j ∈ s, ∀ᵐ d ∂(Measure.pi (fun _ : Fin m => μ)),
      |(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j₀-totalStep d} -
        (Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep d}| ≤ a) :
    |(∫ d, F (iidSplit m r d).1 ∂cond (Measure.pi (fun _ : Fin (m+r) => μ))
        {d | totalStep d=j₀}) -
      (∫ d, F (iidSplit m r d).1 * endpointWindow s w (totalStep d)
        ∂(Measure.pi (fun _ : Fin (m+r) => μ))) /
      (∫ d, endpointWindow s w (totalStep d) ∂(Measure.pi (fun _ : Fin (m+r) => μ)))| ≤
      2*M*a/(Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j₀} := by
  classical
  let k : ℤ → (Fin m → ℕ) → ℝ := fun j d =>
    (Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep d}
  have hk (j : ℤ) : Integrable (k j) (Measure.pi (fun _ : Fin m => μ)) := by
    apply (integrable_const (1:ℝ)).mono' (measurable_of_countable (k j)).aestronglyMeasurable
    filter_upwards [] with d
    change |k j d| ≤ 1
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hki (j : ℤ) : (∫ d, k j d ∂(Measure.pi (fun _ : Fin m => μ))) =
      (Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j} :=
    (iid_site_convolution μ m r j).symm
  have hW : 0 < ∑ j ∈ s, w j := hw₀.trans_le
    (Finset.single_le_sum hw hj₀)
  have hL : 0 < ∫ d, (∑ j ∈ s, w j*k j d) ∂(Measure.pi (fun _ : Fin m => μ)) := by
    rw [integral_finsetSum s (fun j _ => (hk j).const_mul (w j))]
    simp_rw [integral_const_mul,hki]
    apply (mul_pos hw₀ hP).trans_le
    apply Finset.single_le_sum _ hj₀
    intro j hj
    exact mul_nonneg (hw j hj) measureReal_nonneg
  have h := finite_window_stability s w k (k j₀) F hw hW (fun j _ => hk j) (hk j₀)
    (fun _ _ => ae_of_all _ (fun _ => measureReal_nonneg)) (by rwa [hki]) hL
    (by measurability) hM (ae_of_all _ hF) hd
  have he : (∫ d, F (iidSplit m r d).1 ∂cond (Measure.pi (fun _ : Fin (m+r) => μ))
      {d | totalStep d=j₀}) =
      (∫ d, F d*k j₀ d ∂(Measure.pi (fun _ : Fin m => μ))) /
        (∫ d, k j₀ d ∂(Measure.pi (fun _ : Fin m => μ))) := by
    rw [integral_cond_eq_div _ _ (by measurability)]
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
    rw [iid_prefix_test_endpoint μ m r j₀ F hM hF,hki]
  have hn := iid_prefix_test_window μ m r s w F hM hF
  have hden := iid_prefix_test_window μ m r s w (fun _ => 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun _ => by norm_num)
  simp only [one_mul] at hden
  rw [he,hn,hden,hki]
  rw [hki] at h
  simpa only [k] using h


def softCutoff (ε x : ℝ) : ℝ := max 0 (1-|x|/ε)


lemma softCutoff_continuous (ε : ℝ) : Continuous (softCutoff ε) := by
  unfold softCutoff
  fun_prop


lemma softCutoff_nonneg (ε x : ℝ) : 0 ≤ softCutoff ε x := le_max_left _ _


lemma softCutoff_le_one {ε : ℝ} (hε : 0 < ε) (x : ℝ) : softCutoff ε x ≤ 1 := by
  apply max_le (by norm_num)
  have := div_nonneg (abs_nonneg x) hε.le
  linarith


lemma softCutoff_pos_iff {ε x : ℝ} (hε : 0 < ε) :
    0 < softCutoff ε x ↔ |x| < ε := by
  simp only [softCutoff, lt_max_iff, lt_self_iff_false, false_or,
    sub_pos, div_lt_one hε]


lemma softCutoff_support {ε : ℝ} (hε : 0 < ε) :
    Function.support (softCutoff ε) = Set.Ioo (-ε) ε := by
  ext x
  rw [Function.mem_support, ← (softCutoff_nonneg ε x).lt_iff_ne']
  simp only [softCutoff_pos_iff hε, abs_lt,Set.mem_Ioo]


lemma softCutoff_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ω => softCutoff ε (Y ω)) μ := by
  apply (integrable_const (1:ℝ)).mono'
    ((softCutoff_continuous ε).aestronglyMeasurable.comp_aemeasurable hY)
  filter_upwards [] with ω
  change ‖softCutoff ε (Y ω)‖ ≤ (1:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (softCutoff_nonneg _ _)]
  exact softCutoff_le_one hε _


def latticeWindow (N : ℕ) (R : ℝ) : Finset ℤ :=
  (Finset.Icc (-(⌈R⌉₊ : ℤ)) (⌈R⌉₊ : ℤ)).filter
    (fun j => Even ((N:ℤ)+j) ∧ |(j:ℝ)| < R)


lemma mem_latticeWindow_iff (N : ℕ) {R : ℝ} (j : ℤ) :
    j ∈ latticeWindow N R ↔ Even ((N:ℤ)+j) ∧ |(j:ℝ)| < R := by
  classical
  simp only [latticeWindow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hb : |(j:ℝ)| ≤ (⌈R⌉₊:ℝ) := h.2.le.trans (Nat.le_ceil R)
    have hj := abs_le.mp hb
    have hl : -(⌈R⌉₊ : ℤ) ≤ j := by exact_mod_cast hj.1
    have hr : j ≤ (⌈R⌉₊ : ℤ) := by exact_mod_cast hj.2
    exact ⟨⟨hl,hr⟩,h⟩


lemma softCutoff_scaled_pos_iff {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (j : ℤ) :
    0 < softCutoff ε ((j:ℝ)/a) ↔ |(j:ℝ)| < ε*a := by
  rw [softCutoff_pos_iff hε,abs_div,abs_of_pos ha,div_lt_iff₀ ha]


lemma endpointWindow_softCutoff (N : ℕ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (j : ℤ) (hj : Even ((N:ℤ)+j)) :
    endpointWindow (latticeWindow N (ε*a)) (fun k => softCutoff ε ((k:ℝ)/a)) j =
      softCutoff ε ((j:ℝ)/a) := by
  rw [endpointWindow_apply]
  split_ifs with h
  · rfl
  · have hn : ¬|(j:ℝ)| < ε*a := fun hh => h ((mem_latticeWindow_iff N j).mpr ⟨hj,hh⟩)
    have hz := not_lt.mp (fun hh => hn ((softCutoff_scaled_pos_iff hε ha j).mp hh))
    exact (le_antisymm hz (softCutoff_nonneg ε _)).symm


lemma CriticalEvenOffspring.iid_endpointWindow_ae (p : CriticalEvenOffspring)
    (N : ℕ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∀ᵐ d ∂p.iidLaw N,
      endpointWindow (latticeWindow N (ε*a)) (fun k => softCutoff ε ((k:ℝ)/a)) (totalStep d) =
        softCutoff ε ((totalStep d:ℝ)/a) := by
  filter_upwards [p.iid_ae_even N] with d hd
  apply endpointWindow_softCutoff N hε ha
  rw [totalStep_eq_sum_sub]
  have hh : (N:ℤ)+((∑ i, d i : ℕ):ℤ)-(N:ℤ) = ((∑ i, d i : ℕ):ℤ) := by ring
  rw [← add_sub_assoc,hh]
  exact_mod_cast Finset.even_sum d (fun i _ => hd i)


theorem CriticalEvenOffspring.prefix_soft_bound (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (m r : ℕ) (ε : ℝ), 0 < ε →
      Even (((m+(r+1):ℕ):ℤ)-1) →
      1 < ε*(p.sigma*Real.sqrt (m+(r+1))) →
      0 < (p.iidLaw (m+(r+1))).real {d | totalStep d = -1} →
      ∀ (F : (Fin m → ℕ) → ℝ) (M : ℝ), 0 ≤ M → (∀ d, |F d| ≤ M) →
      |(∫ d, F (iidSplit m (r+1) d).1 ∂cond (p.iidLaw (m+(r+1))) {d | totalStep d = -1}) -
        (∫ d, F (iidSplit m (r+1) d).1 *
          softCutoff ε ((totalStep d:ℝ)/(p.sigma*Real.sqrt (m+(r+1)))) ∂p.iidLaw (m+(r+1))) /
        (∫ d, softCutoff ε ((totalStep d:ℝ)/(p.sigma*Real.sqrt (m+(r+1)))) ∂p.iidLaw (m+(r+1)))| ≤
      2*M*((2*E r + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
        (1+ε*(p.sigma*Real.sqrt (m+(r+1)))) /(p.sigma*Real.sqrt (r+1)))/Real.sqrt (r+1)) /
        (p.iidLaw (m+(r+1))).real {d | totalStep d = -1} := by
  obtain ⟨E,hE,hEt,hb⟩ := p.suffix_site_oscillation
  refine ⟨E,hE,hEt,?_⟩
  intro m r ε hε hpar hw hP F M hM hF
  let N := m+(r+1)
  let a := p.sigma*Real.sqrt N
  have ha : 0 < a := mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by dsimp [N]; positivity))
  let s := latticeWindow N (ε*a)
  let w : ℤ → ℝ := fun j => softCutoff ε ((j:ℝ)/a)
  have hmem : (-1:ℤ) ∈ s := by
    apply (mem_latticeWindow_iff N _).mpr
    refine ⟨by simpa only [sub_eq_add_neg,Int.cast_one] using hpar, ?_⟩
    simpa only [Int.cast_neg,Int.cast_one,abs_neg,abs_one,a,N,Nat.cast_add,Nat.cast_one] using hw
  have hwpos : 0 < w (-1) := by
    apply (softCutoff_scaled_pos_iff hε ha (-1)).mpr
    simpa only [Int.cast_neg,Int.cast_one,abs_neg,abs_one,a,N,Nat.cast_add,Nat.cast_one] using hw
  have hdiff (j : ℤ) (hj : j ∈ s) :
      ∀ᵐ d ∂p.iidLaw m,
        |(p.iidLaw (r+1)).real {b | totalStep b=(-1)-totalStep d} -
          (p.iidLaw (r+1)).real {b | totalStep b=j-totalStep d}| ≤
        (2*E r + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          (1+ε*a)/(p.sigma*Real.sqrt (r+1)))/Real.sqrt (r+1) := by
    have hjp := (mem_latticeWindow_iff N j).mp hj
    have hpar' : Even (((m+(r+1):ℕ):ℤ)+(-1)) := by simpa only [sub_eq_add_neg] using hpar
    filter_upwards [hb m r (-1) j hpar' hjp.1] with d hd
    apply hd.trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ (mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity))).le
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.sqrt_nonneg _) (mul_pos p.sigma_pos Real.pi_pos).le)
    calc
      |((-1:ℤ):ℝ)-(j:ℝ)| ≤ |((-1:ℤ):ℝ)|+|(j:ℝ)| := abs_sub _ _
      _ ≤ 1+ε*a := by simp only [Int.cast_neg,Int.cast_one,abs_neg,abs_one]; linarith [hjp.2]
  have h := iid_prefix_window_bound p.law.toMeasure m (r+1) (-1) s w hmem
    (fun j _ => softCutoff_nonneg ε _) hwpos hP F hM hF hdiff
  have he := p.iid_endpointWindow_ae N hε ha
  have hn : (∫ d, F (iidSplit m (r+1) d).1 * endpointWindow s w (totalStep d) ∂p.iidLaw N) =
      ∫ d, F (iidSplit m (r+1) d).1 * softCutoff ε ((totalStep d:ℝ)/a) ∂p.iidLaw N := by
    apply integral_congr_ae
    filter_upwards [he] with d hd
    rw [show endpointWindow s w (totalStep d) = softCutoff ε ((totalStep d:ℝ)/a) from hd]
  have hden := integral_congr_ae he
  change |_- (∫ d, F (iidSplit m (r+1) d).1 * endpointWindow s w (totalStep d) ∂p.iidLaw N) /
    (∫ d, endpointWindow s w (totalStep d) ∂p.iidLaw N)| ≤ _ at h
  rw [hn,hden] at h
  simpa only [a,N,Nat.cast_add,Nat.cast_one,iidLaw] using h

end FKCRT.TreeCoding
end

end OAI
