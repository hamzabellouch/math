import OAI.Probability.GaussianPropeller.SoftMinimum

namespace OAI

universe uX uι uκ

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

def cone (v : κ → E) : Set E := {y | ∀ i, 0 ≤ ⟪v i,y⟫}
def shifted (v : κ → E) (x : E) : Set E := {y | x+y ∈ cone v}
noncomputable def prob (v : κ → E) (x : E) : ℝ := (γ).real (shifted v x)

omit [Nonempty κ] in
lemma measurableSet_shifted [Nonempty κ] (v : κ → E) (x : E) : MeasurableSet (shifted v x) := by
  change MeasurableSet {y : E | ∀ i, 0 ≤ ⟪v i,x+y⟫}
  simpa only [ofPred_forall] using MeasurableSet.iInter (fun i =>
    measurableSet_le (measurable_const : Measurable (fun _ : E => (0:ℝ)))
      (show Measurable (fun y : E => ⟪v i,x+y⟫) by fun_prop))

lemma gaussian_open_pos {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) : 0 < γ U := by
  have hac : (volume : Measure E) ≪ γ := by
    rw [Translation.stdGaussian_density]
    exact withDensity_absolutelyContinuous' Translation.measurable_stdDensity.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (Translation.stdDensity_pos x))))
  by_contra! hz
  have heq : γ U = 0 := le_antisymm hz bot_le
  exact ne_of_gt (hU.measure_pos volume hne) (hac heq)

lemma prob_mem (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (x : E) :
    prob v x ∈ Ioo (0:ℝ) 1 := by
  let U : Set E := {y | ∀ i, 0 < ⟪v i,x+y⟫}
  have hU : IsOpen U := by
    simpa only [U, ofPred_forall] using isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_const : Continuous (fun _ : E => (0:ℝ)))
        (show Continuous (fun y : E => ⟪v i,x+y⟫) by fun_prop))
  have hn : U.Nonempty := ⟨e-x, by simpa only [U, mem_ofPred_eq, show x+(e-x)=e by abel] using he⟩
  have hs : U ⊆ shifted v x := fun y hy i => (hy i).le
  have hp : 0 < (γ).real (shifted v x) := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hU hn).trans_le (measure_mono hs))) (measure_ne_top _ _)
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hv : v i ≠ 0 := by intro hh; simpa only [hh, inner_zero_left, lt_self_iff_false] using he i
  let V : Set E := {y | ⟪v i,x+y⟫ < 0}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hnV : V.Nonempty := by
    refine ⟨-v i-x,?_⟩
    change ⟪v i,x+(-v i-x)⟫ < 0
    rw [show x+(-v i-x)= -v i by abel, inner_neg_right]
    exact neg_neg_of_pos (real_inner_self_pos.mpr hv)
  have hsV : V ⊆ (shifted v x)ᶜ := by
    intro y hy hz
    exact (not_lt_of_ge (hz i)) hy
  have hc : 0 < (γ).real (shifted v x)ᶜ := ENNReal.toReal_pos
    (ne_of_gt ((gaussian_open_pos hV hnV).trans_le (measure_mono hsV))) (measure_ne_top _ _)
  rw [probReal_compl_eq_one_sub (measurableSet_shifted v x)] at hc
  exact ⟨hp, by change (γ).real (shifted v x) < 1; linarith only [hc]⟩

lemma gaussian_hyperplane_null (z : E) (hz : z ≠ 0) (c : ℝ) :
    γ {x | ⟪z,x⟫ = c} = 0 := by
  let L : StrongDual ℝ E := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z,z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L γ).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass (gaussianReal (∫ x, L x ∂γ) (variance L γ).toNNReal) :=
    nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal (μ := γ) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c), measure_singleton] at h
  exact h

omit [Nonempty κ] in
lemma ae_no_boundary [Nonempty κ] (v : κ → E) (hv : ∀ i, v i ≠ 0) (x : E) :
    ∀ᵐ y ∂γ, ∀ i, ⟪v i,x+y⟫ ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  have hh := gaussian_hyperplane_null (v i) (hv i) (-⟪v i,x⟫)
  have hh' : ∀ᵐ y ∂γ, ⟪v i,y⟫ ≠ -⟪v i,x⟫ := by
    rw [ae_iff]
    simpa only [not_not] using hh
  filter_upwards [hh'] with y hy
  rw [inner_add_right]
  intro hzero
  apply hy
  linarith only [hzero]

lemma cdf_softmin_limit (v : κ → E) (y : E) (hy : ∀ i, ⟪v i,y⟫ ≠ 0) :
    Tendsto (fun n : ℕ => Φ (SoftMin.value (fun i => (n:ℝ) • v i) y)) atTop
      (𝓝 ((cone v).indicator (fun _ => (1:ℝ)) y)) := by
  classical
  by_cases hmem : y ∈ cone v
  · rw [Set.indicator_of_mem hmem]
    exact tendsto_Φ_atTop.comp (SoftMin.value_tendsto_atTop v y
      (fun i => lt_of_le_of_ne (hmem i) (Ne.symm (hy i))))
  · rw [Set.indicator_of_notMem hmem]
    simp only [cone, mem_ofPred_eq, not_forall, not_le] at hmem
    obtain ⟨i,hi⟩ := hmem
    exact tendsto_Φ_atBot.comp (SoftMin.value_tendsto_atBot v y i hi)

lemma prob_limit (v : κ → E) (hv : ∀ i, v i ≠ 0) (x : E) :
    Tendsto (fun n : ℕ => HeatConvolution.heat
      (fun y => Φ (SoftMin.value (fun i => (n:ℝ) • v i) y)) 1 x) atTop (𝓝 (prob v x)) := by
  classical
  have hlim := tendsto_integral_of_dominated_convergence (μ := γ) (bound := fun _ : E => (1:ℝ))
    (F := fun n : ℕ => fun y : E => Φ (SoftMin.value (fun i => (n:ℝ) • v i) (x+y)))
    (f := fun y : E => (cone v).indicator (fun _ => (1:ℝ)) (x+y)) ?_ (integrable_const _) ?_ ?_
  · convert hlim using 1
    · funext n; simp only [HeatConvolution.heat, Real.sqrt_one, one_smul]
    · rw [show (fun y : E => (cone v).indicator (fun _ => (1:ℝ)) (x+y)) =
        (shifted v x).indicator (fun _ => (1:ℝ)) by
          funext y; rfl]
      rw [integral_indicator (measurableSet_shifted v x), setIntegral_const]
      simp only [prob, smul_eq_mul, mul_one]
  · intro n
    have hc : Continuous (SoftMin.value (fun i => (n:ℝ) • v i)) :=
      continuous_iff_continuousAt.mpr (fun y => (SoftMin.value_fderiv _ y).continuousAt)
    exact (continuous_Φ.comp (hc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (fun y => SmoothCDF.cdf_bound _ _)
  · filter_upwards [ae_no_boundary v hv x] with y hy
    exact cdf_softmin_limit v (x+y) hy

lemma quantile_prob_concave (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) :
    ConcaveOn ℝ univ (fun x => q (prob v x)) := by
  have hv : ∀ i, v i ≠ 0 := by
    intro i hi; simpa only [hi, inner_zero_left, lt_self_iff_false] using he i
  have hc (n : ℕ) : ConcaveOn ℝ univ (qheat (SoftMin.value (fun i => (n:ℝ) • v i)) 1) := by
    let w : κ → E := fun i => (n:ℝ) • v i
    let L : ℝ≥0 := ∑ i, ‖w i‖₊
    have hL (i : κ) : ‖w i‖ ≤ L := by
      exact_mod_cast (Finset.single_le_sum (f := fun j => ‖w j‖₊) (fun j _ => bot_le) (Finset.mem_univ i))
    exact qheat_concave (SoftMin.value_fderiv w) (SoftMin.grad_fderiv w)
      (SoftMin.continuous_hess w) (SoftMin.grad_bound w hL)
      (SoftMin.hess_bound w L.coe_nonneg hL) (SoftMin.value_concave w) (by norm_num)
  have ht (x : E) : Tendsto (fun n : ℕ => qheat (SoftMin.value (fun i => (n:ℝ) • v i)) 1 x)
      atTop (𝓝 (q (prob v x))) := (continuousAt_q (prob_mem v e he x)).tendsto.comp (prob_limit v hv x)
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  exact le_of_tendsto_of_tendsto ((ht x).const_smul a |>.add ((ht y).const_smul b))
    (ht (a•x+b•y)) (Filter.Eventually.of_forall (fun n => (hc n).2 (mem_univ x) (mem_univ y) ha hb hab))

end GaussianPropeller.EhrhardCone

namespace GaussianPropeller.Quantile

lemma Φ_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  unfold Φ
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

lemma integrable_mul_φ : Integrable (fun x : ℝ => x*φ x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [φ]
  rw [show -x^2/2 = -(1/2:ℝ)*x^2 by ring]
  ring

lemma tendsto_φ_atBot : Tendsto φ atBot (𝓝 0) := by
  have htop : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0))
  have ht : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) atBot (𝓝 0) := by
    simpa only [Function.comp_def, neg_sq] using htop.comp tendsto_neg_atBot_atTop
  convert ht.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
  · funext x; unfold φ; congr 2; ring
  · simp only [mul_zero]

lemma left_first_moment (a : ℝ) : ∫ x in Iic a, x*φ x = -φ a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -φ x) (x*φ x) x := by
    convert (hasDerivAt_φ x).neg using 1
    ring
  simpa only [neg_zero, sub_zero, Pi.neg_apply] using integral_Iic_of_hasDerivAt_of_tendsto
    (continuous_φ.neg.continuousWithinAt) (fun x _ => hd x)
    integrable_mul_φ.integrableOn (tendsto_φ_atBot.neg)

lemma integral_positive_cdf (a : ℝ) :
    ∫ x : ℝ, max (a-x) 0 ∂gaussianReal 0 1 = a*Φ a+φ a := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp only [show ∀ x : ℝ, gaussianPDFReal 0 1 x = φ x by
    intro x; simp only [gaussianPDFReal, φ, NNReal.coe_one, mul_one, sub_zero], smul_eq_mul]
  have heq : ∫ x : ℝ, φ x * max (a-x) 0 = ∫ x in Iic a, (a-x)*φ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iic a)]
    · exact setIntegral_congr_fun measurableSet_Iic (fun x hx => by
        rw [max_eq_left (sub_nonneg.mpr hx)]; ring)
    · intro x hx
      simp only [mem_Iic, not_le] at hx
      rw [max_eq_right (sub_nonpos.mpr hx.le), mul_zero]
  rw [heq]
  simp_rw [sub_mul]
  rw [integral_sub (integrable_φ.const_mul a).integrableOn integrable_mul_φ.integrableOn,
    integral_const_mul, left_first_moment]
  simp only [Φ, sub_neg_eq_add]

lemma tail_integrable {X : Type uX} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hi : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioi 0) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (show Antitone (fun t : ℝ => μ {x | t ≤ f x}) from
      fun _ _ hst => measure_mono (fun _ h => hst.trans h)).measurable.aemeasurable
  · rw [← lintegral_eq_lintegral_meas_le μ hn hi.aemeasurable]
    exact hi.lintegral_lt_top.ne

lemma integral_cdf_tail (a c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Φ (a-c*u)) (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), Φ (a-c*u)) = (a*Φ a+φ a)/c := by
  let f : ℝ → ℝ := fun x => max (a-x) 0 / c
  have hf : Integrable f (gaussianReal 0 1) := by
    exact (((integrable_const a).sub (IsGaussian.integrable_id (μ := gaussianReal 0 1))).sup
      (integrable_const 0)).div_const c
  have hn : 0 ≤ᵐ[gaussianReal 0 1] f := ae_of_all _ (fun x => div_nonneg (le_max_right _ _) hc.le)
  have heq (u : ℝ) (hu : 0 < u) : (gaussianReal 0 1).real {x | u ≤ f x} = Φ (a-c*u) := by
    rw [Φ_eq_gaussianReal]
    congr 1
    ext x
    simp only [mem_ofPred_eq, mem_Iic, f, le_div_iff₀ hc, le_max_iff]
    have hh : ¬ u*c ≤ 0 := not_le.mpr (mul_pos hu hc)
    simp only [hh, or_false]
    constructor <;> intro h <;> nlinarith only [h]
  have hi : IntegrableOn (fun u : ℝ => Φ (a-c*u)) (Ioi 0) :=
    (tail_integrable hf hn).congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => heq u hu))
  refine ⟨hi,?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq,
    ← hf.integral_eq_integral_meas_le hn]
  rw [show f = fun x => max (a-x) 0 / c from rfl, integral_div, integral_positive_cdf]

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

lemma measurableSet_cone (v : κ → E) : MeasurableSet (cone v) := by
  simpa only [shifted, zero_add, ofPred_mem_eq] using measurableSet_shifted v 0

omit [Fintype κ] [Nonempty κ] in
lemma prob_zero [Fintype κ] [Nonempty κ] (v : κ → E) : prob v 0 = (γ).real (cone v) := by
  simp only [prob, shifted, zero_add, ofPred_mem_eq]

lemma prob_line_deriv (v : κ → E) (h : E) :
    HasDerivAt (fun u : ℝ => prob v (-u • h))
      (-⟪h, ∫ x in cone v, x ∂γ⟫) 0 := by
  have heq (u : ℝ) : prob v (-u • h) =
      ((γ).map (fun x => x-u•h)).real (cone v) := by
    unfold prob
    rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) (measurableSet_cone v)]
    apply congrArg ENNReal.toReal
    apply congrArg γ
    ext x
    change (-u•h+x ∈ cone v) ↔ (x-u•h ∈ cone v)
    rw [show -u•h+x = x-u•h by simp only [neg_smul, sub_eq_add_neg, add_comm]]
  simp_rw [heq]
  exact Translation.translation_derivative h (cone v) (measurableSet_cone v)

lemma prob_tangent (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (h : E) (u : ℝ) :
    prob v (-u • h) ≤ Φ (q (prob v 0)-
      (⟪h, ∫ x in cone v, x ∂γ⟫ / φ (q (prob v 0)))*u) := by
  have hc : ConcaveOn ℝ univ (fun t : ℝ => q (prob v (-t•h))) := by
    refine ⟨convex_univ,?_⟩
    intro s _ t _ a b ha hb hab
    have hh := (quantile_prob_concave v e he).2 (mem_univ (-s•h)) (mem_univ (-t•h)) ha hb hab
    change a * q (prob v (-s•h))+b * q (prob v (-t•h)) ≤ q (prob v (-(a*s+b*t)•h))
    rw [show -(a*s+b*t)•h = a•(-s•h)+b•(-t•h) by module]
    exact hh
  have hd := (hasDerivAt_q (prob_mem v e he (-(0:ℝ)•h))).comp (0:ℝ) (prob_line_deriv v h)
  simp only [neg_zero, zero_smul] at hd
  have ht := concave_le_tangent hc (mem_univ 0) (mem_univ u) hd
  simp only [neg_zero, zero_smul, sub_zero] at ht
  have ht' : q (prob v (-u•h)) ≤ q (prob v 0)-
      (⟪h, ∫ x in cone v, x ∂γ⟫ / φ (q (prob v 0)))*u := by
    calc
      _ ≤ q (prob v 0) + (φ (q (prob v 0)))⁻¹ * (-⟪h, ∫ x in cone v, x ∂γ⟫) * u := ht
      _ = _ := by ring
  have hh := strictMono_Φ.monotone ht'
  rwa [Φ_q (prob_mem v e he (-u•h))] at hh

lemma integral_prob_upper (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫)
    (h : E) (hβ : 0 < ⟪h, ∫ x in cone v, x ∂γ⟫) :
    (∫ u in Ioi (0:ℝ), prob v (-u • h)) ≤
      φ (q (prob v 0)) * (q (prob v 0)*prob v 0+φ (q (prob v 0))) /
      ⟪h, ∫ x in cone v, x ∂γ⟫ := by
  let a := q (prob v 0)
  let c := ⟪h, ∫ x in cone v, x ∂γ⟫ / φ a
  have hc : 0 < c := div_pos hβ (φ_pos a)
  calc
    _ ≤ ∫ u in Ioi (0:ℝ), Φ (a-c*u) := integral_mono_of_nonneg
      (ae_of_all (volume.restrict (Ioi (0:ℝ))) (fun u => measureReal_nonneg))
      (integral_cdf_tail a c hc).1
      (ae_of_all _ (prob_tangent v e he h))
    _ = (a*Φ a+φ a)/c := (integral_cdf_tail a c hc).2
    _ = _ := by
      dsimp [a,c]
      rw [Φ_q (prob_mem v e he 0)]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

end GaussianPropeller.EhrhardCone

end OAI
