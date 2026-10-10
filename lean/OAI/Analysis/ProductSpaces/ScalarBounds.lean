import OAI.Analysis.ProductSpaces.WeakNullity

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma gaussianTail_nonneg (r : ℝ) : 0 ≤ gaussianTail r := ENNReal.toReal_nonneg

lemma gaussianTail_le_one (r : ℝ) : gaussianTail r ≤ 1 := by
  exact (measureReal_mono (subset_univ _) : (gaussianReal 0 1).real _ ≤ _).trans_eq (by simp)

lemma gaussianTail_antitone : Antitone gaussianTail := by
  intro a b hab
  exact measureReal_mono (fun x hx => hab.trans hx)

lemma gaussianTail_pos (r : ℝ) : 0 < gaussianTail r := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
  apply lt_of_lt_of_le (b := gaussianReal 0 1 (Ioo (|r| + 1) (|r| + 2)))
  · apply pos_iff_ne_zero.mpr
    intro hzero
    have hz := (gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) (by norm_num)) hzero
    have hp : (0 : ℝ≥0∞) < volume (Ioo (|r| + 1) (|r| + 2)) := by simp
    exact hp.ne' hz
  · apply measure_mono
    intro x hx
    exact le_trans (le_abs_self r) (le_trans (by linarith [hx.1]) (le_abs_self x))

lemma integrable_gaussian_abs_excess (K : ℝ) :
    Integrable (fun x : ℝ => max (|x| - 2 * K) 0) (gaussianReal 0 1) := by
  exact (((memLp_id_gaussianReal 1).integrable (by norm_num)).abs.sub (integrable_const _)).sup
    (integrable_const 0)

lemma excessConstant_pos (K : ℝ) : 0 < excessConstant K := by
  apply mul_pos (by norm_num)
  apply (integral_pos_iff_support_of_nonneg (fun x => le_max_right _ _)
    (integrable_gaussian_abs_excess K)).mpr
  apply lt_of_lt_of_le (b := gaussianReal 0 1 {x : ℝ | 2 * |K| + 1 ≤ |x|})
  · have h := gaussianTail_pos (2 * |K| + 1)
    exact ENNReal.toReal_pos_iff.mp h |>.1
  · apply measure_mono
    intro x hx
    apply Function.mem_support.mpr
    change 2 * |K| + 1 ≤ |x| at hx
    have hp : 0 < |x| - 2 * K := by nlinarith [le_abs_self K]
    exact (lt_of_lt_of_le hp (le_max_left _ _)).ne'

lemma gaussian_integral_sq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable] at h
  simpa using h

lemma gaussian_integral_fourth : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := by
    simpa using mgf_fun_id_gaussianReal (μ := 0) (v := 1)
  have d1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [_root_.deriv_exp (by fun_prop)]
    rw [deriv_div_const, deriv_pow_field]
    norm_num
    ring
  have d2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    change _ + t * (deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) t) = _
    rw [d1]
    simp only [deriv_id'']
    ring
  have d3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    change _ + (1 + t ^ 2) * (deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) t) = _
    rw [d1]
    rw [deriv_const_add, deriv_pow_field]
    norm_num
    ring
  have d4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) 0 = 3 := by
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    have hp : deriv (fun t : ℝ => 3 * t + t ^ 3) 0 = 3 := by
      rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const_mul 3 (by fun_prop), deriv_pow_field]
      norm_num
    rw [hp]
    norm_num
  have hiff : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by simp
  have he := iteratedDeriv_mgf_zero hiff 4
  rw [hmgf, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    d1, d2, d3, d4] at he
  exact he.symm

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integral_mul_sq_le [IsProbabilityMeasure μ] (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  have hfg : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hω hω'
    simp only [hω, hω', RCLike.inner_apply, conj_trivial]
    ring
  have hff : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ ω, f ω ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hgg : inner ℝ (hg.toLp g) (hg.toLp g) = ∫ ω, g ω ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with ω hω
    rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  simpa only [hfg, hff, hgg, pow_two] using h

variable [IsProbabilityMeasure μ]

/-- A second-moment lower bound on the probability of exceeding half the mean. -/
lemma second_moment_tail_bound (V : Ω → ℝ) (hV : MemLp V 2 μ)
    (hVmeas : Measurable V) (hpos : ∀ ω, 0 ≤ V ω)
    (a b : ℝ) (ha : 0 ≤ a) (hb : a < b) (hmean : b ≤ ∫ ω, V ω ∂μ) :
    (b - a) ^ 2 ≤ (∫ ω, V ω ^ 2 ∂μ) * μ.real {ω | a ≤ V ω} := by
  let A : Set Ω := {ω | a ≤ V ω}
  have hm : MeasurableSet A := measurableSet_le measurable_const hVmeas
  have hint : Integrable V μ := hV.integrable (by norm_num)
  have hind : MemLp (A.indicator (fun _ : Ω => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hm
  have hcs := integral_mul_sq_le V _ hV hind
  have hg : (∫ ω, (A.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ 2 ∂μ) = μ.real A := by
    have he : (fun ω => (A.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ 2) = A.indicator (fun _ => 1) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [hω]
    rw [he, integral_indicator hm]
    simp
  have hf : (∫ ω, V ω * A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = ∫ ω in A, V ω ∂μ := by
    rw [← integral_indicator hm]
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [hg, hf] at hcs
  have hlower : b - a ≤ ∫ ω in A, V ω ∂μ := by
    have hcompl : (∫ ω in Aᶜ, V ω ∂μ) ≤ a := by
      calc
        (∫ ω in Aᶜ, V ω ∂μ) ≤ ∫ _ in Aᶜ, a ∂μ := by
          apply integral_mono_ae hint.restrict (integrable_const _)
          filter_upwards [ae_restrict_mem hm.compl] with ω hω
          exact le_of_lt (not_le.mp hω)
        _ = a * μ.real Aᶜ := by simp [mul_comm]
        _ ≤ a * 1 := mul_le_mul_of_nonneg_left measureReal_le_one ha
        _ = a := mul_one _
    have he := integral_add_compl hm hint
    linarith
  exact ((sq_le_sq₀ (sub_nonneg.mpr hb.le)
    (integral_nonneg (μ := μ.restrict A) (f := V) hpos)).2 hlower).trans hcs

end SecondMoment
end IndependentProducts

namespace IndependentProducts

/-- Polarization on one independent standard Gaussian pair. -/
def gaussianRotate (z : ℝ × ℝ) : ℝ × ℝ :=
  ((Real.sqrt 2)⁻¹ * (z.1 + z.2), (Real.sqrt 2)⁻¹ * (z.1 - z.2))

lemma gaussianRotate_measurable : Measurable gaussianRotate := by unfold gaussianRotate; fun_prop

lemma measurePreserving_gaussianRotate : MeasurePreserving gaussianRotate
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let P := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hxf : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 0 1) P := measurePreserving_fst.hasLaw
  have hyf : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) P := measurePreserving_snd.hasLaw
  have hx := hxf.hasGaussianLaw
  have hy := hyf.hasGaussianLaw
  have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd P :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hjoint0 := hind.hasGaussianLaw hx hy
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((Real.sqrt 2)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
      ((Real.sqrt 2)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hjoint : HasGaussianLaw gaussianRotate P := hjoint0.map_fun L
  have hcov0 : cov[Prod.fst, Prod.snd; P] = 0 := hind.covariance_eq_zero hx.memLp_two hy.memLp_two
  have hcov1 : cov[Prod.snd, Prod.fst; P] = 0 := by rwa [covariance_comm]
  have hxm : (∫ z, z.1 ∂P) = (0 : ℝ) := hxf.integral_eq.trans (by simp)
  have hym : (∫ z, z.2 ∂P) = (0 : ℝ) := hyf.integral_eq.trans (by simp)
  have hxv : Var[Prod.fst; P] = 1 := hxf.variance_eq.trans (by simp)
  have hyv : Var[Prod.snd; P] = 1 := hyf.variance_eq.trans (by simp)
  have hscale : ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcov : cov[fun z => (gaussianRotate z).1, fun z => (gaussianRotate z).2; P] = 0 := by
    simp only [gaussianRotate, covariance_const_mul_left, covariance_const_mul_right]
    have hz : cov[(Prod.fst : ℝ × ℝ → ℝ) + Prod.snd, Prod.fst - Prod.snd; P] = 0 := by
      rw [covariance_sub_right (hx.memLp_two.add hy.memLp_two) hx.memLp_two hy.memLp_two,
        covariance_add_left hx.memLp_two hy.memLp_two hx.memLp_two,
        covariance_add_left hx.memLp_two hy.memLp_two hy.memLp_two,
        covariance_self hx.aemeasurable, covariance_self hy.aemeasurable, hcov0, hcov1, hxv, hyv]
      norm_num
    change (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * cov[Prod.fst + Prod.snd, Prod.fst - Prod.snd; P]) = 0
    rw [hz]
    ring
  have hrotind : IndepFun (fun z => (gaussianRotate z).1) (fun z => (gaussianRotate z).2) P :=
    hjoint.indepFun_of_covariance_eq_zero hcov
  have ham : (∫ z, (gaussianRotate z).1 ∂P) = (0 : ℝ) := by
    change (∫ z : ℝ × ℝ, (Real.sqrt 2)⁻¹ * (z.1 + z.2) ∂P) = 0
    rw [integral_const_mul, integral_add hx.integrable hy.integrable, hxm, hym]
    ring
  have hcm : (∫ z, (gaussianRotate z).2 ∂P) = (0 : ℝ) := by
    change (∫ z : ℝ × ℝ, (Real.sqrt 2)⁻¹ * (z.1 - z.2) ∂P) = 0
    rw [integral_const_mul, integral_sub hx.integrable hy.integrable, hxm, hym]
    ring
  have hav : Var[fun z => (gaussianRotate z).1; P] = 1 := by
    rw [show (fun z => (gaussianRotate z).1) =
      (fun z : ℝ × ℝ => (Real.sqrt 2)⁻¹ * (z.1 + z.2)) from rfl,
      variance_const_mul, variance_fun_add hx.memLp_two hy.memLp_two, hcov0, hxv, hyv, hscale]
    norm_num
  have hcv : Var[fun z => (gaussianRotate z).2; P] = 1 := by
    rw [show (fun z => (gaussianRotate z).2) =
      (fun z : ℝ × ℝ => (Real.sqrt 2)⁻¹ * (z.1 - z.2)) from rfl,
      variance_const_mul, variance_fun_sub hx.memLp_two hy.memLp_two, hcov0, hxv, hyv, hscale]
    norm_num
  have hamap := hjoint.fst.map_eq_gaussianReal
  have hcmap := hjoint.snd.map_eq_gaussianReal
  change P.map (fun z => (gaussianRotate z).1) = gaussianReal (∫ z, (gaussianRotate z).1 ∂P) (Var[fun z => (gaussianRotate z).1; P]).toNNReal at hamap
  change P.map (fun z => (gaussianRotate z).2) = gaussianReal (∫ z, (gaussianRotate z).2 ∂P) (Var[fun z => (gaussianRotate z).2; P]).toNNReal at hcmap
  rw [ham, hav] at hamap
  rw [hcm, hcv] at hcmap
  refine ⟨gaussianRotate_measurable, ?_⟩
  change P.map (fun z => ((gaussianRotate z).1, (gaussianRotate z).2)) = _
  rw [IndepFun.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop) hrotind, hamap, hcmap]
  norm_num

lemma gaussian_polarization (z : ℝ × ℝ) :
    z.1 ^ 2 - z.2 ^ 2 = 2 * (gaussianRotate z).1 * (gaussianRotate z).2 := by
  have h : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hh : Real.sqrt 2 ≠ 0 := by positivity
  dsimp [gaussianRotate]
  field_simp
  nlinarith

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

lemma map_gaussian_finset_sum (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (v : ι → ℝ≥0) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    (s : Finset ι) : P.map (fun ω => ∑ i ∈ s, X i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simp [Measure.map_const, gaussianReal_zero_var]
  | @insert i s hi ih =>
    have hind' := (hind.indepFun_finsetSum_of_notMem hX hi).symm
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hind'
      ⟨(hX i).aemeasurable, hlaw i⟩
      ⟨(by fun_prop), by simpa only [Finset.sum_fn] using ih⟩
    simpa only [Finset.sum_insert hi, Finset.sum_fn, Pi.add_def, zero_add] using hsum

variable [Fintype ι]

lemma map_gaussian_weighted_sum (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => ∑ i, a i * x i) =
      gaussianReal 0 (∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _)) := by
  let P := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have hind : iIndepFun (fun i : ι => fun x : ι → ℝ => a i * x i) P :=
    iIndepFun_pi (fun i => (measurable_const.mul measurable_id).aemeasurable)
  have hlaw : ∀ i, P.map (fun x => a i * x i) = gaussianReal 0 (NNReal.mk (a i ^ 2) (sq_nonneg _)) := by
    intro i
    have he : (fun x : ι → ℝ => a i * x i) = (fun z => a i * z) ∘ Function.eval i := rfl
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq,
      gaussianReal_map_const_mul]
    apply congrArg₂ gaussianReal
    · simp
    · ext
      change a i ^ 2 * 1 = a i ^ 2
      ring
  exact map_gaussian_finset_sum _ (fun _ => by fun_prop) hind _ hlaw Finset.univ

end GaussianSum
end IndependentProducts

end

end OAI
