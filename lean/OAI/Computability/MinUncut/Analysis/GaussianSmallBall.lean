import Mathlib
import OAI.Computability.MinUncut.Encoding.UniformEncoding

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
namespace MinUncut.GaussianBudget

lemma pdf_le_one {v : ℝ≥0} (hv : 1≤v) (x : ℝ) : gaussianPDFReal 0 v x≤1 := by
  have hvR : (1:ℝ)≤v := by exact_mod_cast hv
  have hs : 1≤Real.sqrt (2*Real.pi*(v:ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have he : Real.exp (-(x-0)^2/(2*(v:ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  rw [gaussianPDFReal]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs))

lemma small_ball {v : ℝ≥0} (hv : 1≤v) {r : ℝ} (hr : 0≤r) :
    (gaussianReal 0 v).real {x : ℝ | |x|≤r} ≤ 2*r := by
  have hv0 : v≠0 := by linarith
  have he : {x : ℝ | |x|≤r}=Set.Icc (-r) r := by ext x; simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  rw [he,Measure.real,gaussianReal_apply_eq_integral 0 hv0]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 v x))]
  calc
    _ ≤ ∫ _ : ℝ in Set.Icc (-r) r, (1:ℝ) :=
      integral_mono (integrable_gaussianPDFReal 0 v).integrableOn (integrable_const 1) (fun x => pdf_le_one hv x)
    _ = 2*r := by simp only [setIntegral_const,smul_eq_mul,mul_one,Real.volume_real_Icc]; rw [max_eq_left (by linarith)]; ring

def betweenIndicator (x y : ℝ) : ℝ := if |x|≤|y| then 1 else 0

lemma between_measurable : Measurable (fun p : ℝ×ℝ => betweenIndicator p.1 p.2) := by
  unfold betweenIndicator
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const measurable_const

lemma between_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω => betweenIndicator (X ω) (Y ω)) μ := by
  apply Integrable.of_bound (between_measurable.comp (hX.prodMk hY)).aestronglyMeasurable 1
  filter_upwards [] with x
  change |betweenIndicator (X x) (Y x)|≤1
  unfold betweenIndicator
  split_ifs <;> norm_num

lemma integral_between {v : ℝ≥0} (hv : 1≤v) (y : ℝ) :
    (∫ x, betweenIndicator x y ∂gaussianReal 0 v) ≤ 2*|y| := by
  have he : (fun x => betweenIndicator x y) = Set.indicator {x : ℝ | |x|≤|y|} (fun _ => (1:ℝ)) := by
    ext x; simp only [betweenIndicator,Set.indicator_apply,Set.mem_ofPred_eq]
  rw [he,integral_indicator (measurableSet_le (by fun_prop) measurable_const),setIntegral_const]
  simpa using small_ball hv (abs_nonneg y)

lemma independent_small_ball {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω→ℝ} (hX : Measurable X) (hY : Measurable Y) (hYI : Integrable Y μ)
    (hXY : IndepFun X Y μ) {v : ℝ≥0} (hv : 1≤v) (hlaw : μ.map X=gaussianReal 0 v) :
    (∫ ω, betweenIndicator (X ω) (Y ω) ∂μ) ≤ 2*(∫ ω, |Y ω| ∂μ) := by
  have hmap := hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hi : Integrable (fun p : ℝ×ℝ => betweenIndicator p.1 p.2) ((μ.map X).prod (μ.map Y)) :=
    between_integrable measurable_fst measurable_snd
  have he : (∫ ω, betweenIndicator (X ω) (Y ω) ∂μ) =
      ∫ y, ∫ x, betweenIndicator x y ∂(μ.map X) ∂(μ.map Y) := by
    rw [← integral_map (hX.prodMk hY).aemeasurable between_measurable.aestronglyMeasurable,hmap,
      integral_prod_symm _ hi]
  rw [he,hlaw]
  have hiY : Integrable (fun y : ℝ => 2*|y|) (μ.map Y) := by
    rw [integrable_map_measure (by fun_prop) hY.aemeasurable]
    exact hYI.abs.const_mul 2
  have hiB : Integrable (fun y => ∫ x, betweenIndicator x y ∂gaussianReal 0 v) (μ.map Y) := by
    rw [hlaw] at hi
    exact hi.integral_prod_right
  calc
    _ ≤ ∫ y, 2*|y| ∂(μ.map Y) := integral_mono hiB hiY (integral_between hv)
    _ = _ := by rw [integral_const_mul,integral_map hY.aemeasurable (by fun_prop)]

attribute [local instance] Classical.propDecidable

def signFailure (x y : ℝ) : ℝ := if (0 ≤ x ↔ 0 ≤ y) then 0 else 1

lemma signFailure_range (x y : ℝ) : 0 ≤ signFailure x y ∧ signFailure x y ≤ 1 := by
  unfold signFailure
  split_ifs <;> norm_num

lemma signFailure_measurable : Measurable (fun p : ℝ×ℝ => signFailure p.1 p.2) := by
  unfold signFailure
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le measurable_const measurable_fst).iff
    (measurableSet_le measurable_const measurable_snd)

lemma signFailure_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω => signFailure (X ω) (Y ω)) μ := by
  apply Integrable.of_bound (signFailure_measurable.comp (hX.prodMk hY)).aestronglyMeasurable 1
  filter_upwards [] with ω
  change ‖signFailure (X ω) (Y ω)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (signFailure_range _ _).1]
  exact (signFailure_range _ _).2

lemma signFailure_add_le (x y : ℝ) : signFailure x (x+y) ≤ betweenIndicator x y := by
  unfold signFailure betweenIndicator
  split_ifs with h h' h'
  all_goals try norm_num
  exfalso
  apply h'
  have hh : (x < 0 ∧ 0 ≤ x+y) ∨ (0 ≤ x ∧ x+y < 0) := by
    by_cases hx : 0 ≤ x
    · right; refine ⟨hx,lt_of_not_ge ?_⟩; intro hy; exact h (iff_of_true hx hy)
    · left; refine ⟨lt_of_not_ge hx,?_⟩; by_contra hy; exact h (iff_of_false hx hy)
  rcases hh with hh|hh
  · rw [abs_of_neg hh.1,abs_of_nonneg (by linarith : 0 ≤ y)]; linarith
  · rw [abs_of_nonneg hh.1,abs_of_neg (by linarith : y < 0)]; linarith

lemma signFailure_sumdiff_le (x y : ℝ) : signFailure x y ≤ betweenIndicator (x+y) (x-y) := by
  unfold signFailure betweenIndicator
  split_ifs with h h' h'
  all_goals try norm_num
  exfalso
  apply h'
  have hh : (x < 0 ∧ 0 ≤ y) ∨ (0 ≤ x ∧ y < 0) := by
    by_cases hx : 0 ≤ x
    · right; refine ⟨hx,lt_of_not_ge ?_⟩; intro hy; exact h (iff_of_true hx hy)
    · left; refine ⟨lt_of_not_ge hx,?_⟩; by_contra hy; exact h (iff_of_false hx hy)
  rcases hh with hh|hh
  · rw [abs_of_neg (by linarith : x-y < 0)]
    rw [abs_le]; constructor <;> linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
    rw [abs_le]; constructor <;> linarith

lemma signFailure_triangle (x y z : ℝ) :
    signFailure x z ≤ signFailure x y+signFailure y z := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y <;> by_cases hz : 0 ≤ z <;>
    simp [signFailure,hx,hy,hz]

lemma integral_abs_le_sqrt_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∫ ω, |X ω| ∂μ) ≤ Real.sqrt (∫ ω, X ω^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num : (2:ℝ).HolderConjugate 2)
    (by simpa using hX) (by simpa using (memLp_const (1:ℝ) (p := 2) (μ := μ)))
  simpa only [Real.norm_eq_abs,abs_one,mul_one,Real.rpow_two,sq_abs,
    one_pow,integral_const,probReal_univ,one_smul,Real.one_rpow,← Real.sqrt_eq_rpow,Real.sqrt_one,mul_one] using h

lemma independent_sign_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hy : MemLp Y 2 μ)
    (hXY : IndepFun X Y μ) {v : ℝ≥0} (hv : 1 ≤ v) (hlaw : μ.map X=gaussianReal 0 v) :
    (∫ ω, signFailure (X ω) (X ω+Y ω) ∂μ) ≤ 2*Real.sqrt (∫ ω, Y ω^2 ∂μ) := by
  calc
    _ ≤ ∫ ω, betweenIndicator (X ω) (Y ω) ∂μ :=
      integral_mono (signFailure_integrable hX (hX.add hY)) (between_integrable hX hY) (fun ω => signFailure_add_le _ _)
    _ ≤ 2*(∫ ω, |Y ω| ∂μ) := independent_small_ball hX hY (hy.integrable (by norm_num)) hXY hv hlaw
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_sq hy) (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma inner_hasGaussianLaw (v : E) : HasGaussianLaw (fun c : E => ⟪v,c⟫) (stdGaussian E) := by
  exact IsGaussian.hasGaussianLaw_id.map (innerSL ℝ v)

lemma inner_law (v : E) : (stdGaussian E).map (fun c : E => ⟪v,c⟫) =
    gaussianReal 0 ⟨‖v‖^2,sq_nonneg _⟩ := by
  have h := (inner_hasGaussianLaw v).map_eq_gaussianReal
  have hm : (∫ c : E, ⟪v,c⟫ ∂stdGaussian E)=0 := integral_strongDual_stdGaussian (innerSL ℝ v)
  have hv : Var[fun c : E => ⟪v,c⟫;stdGaussian E]=‖v‖^2 := by
    change Var[⇑(innerSL ℝ v);stdGaussian E]=‖v‖^2
    rw [variance_dual_stdGaussian,innerSL_apply_norm]
  rw [hm,hv] at h
  convert h using 2
  congr 1
  apply Subtype.ext
  simp

lemma inner_second_moment (v : E) : (∫ c : E, ⟪v,c⟫^2 ∂stdGaussian E)=‖v‖^2 := by
  have h := variance_eq_sub (inner_hasGaussianLaw v).memLp_two
  have hm : (∫ c : E, ⟪v,c⟫ ∂stdGaussian E)=0 := integral_strongDual_stdGaussian (innerSL ℝ v)
  have hv : Var[fun c : E => ⟪v,c⟫;stdGaussian E]=‖v‖^2 := by
    change Var[⇑(innerSL ℝ v);stdGaussian E]=‖v‖^2
    rw [variance_dual_stdGaussian,innerSL_apply_norm]
  simpa only [hm,hv,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero,Pi.pow_apply] using h.symm

lemma orthogonal_indep {v w : E} (hvw : ⟪v,w⟫=0) :
    IndepFun (fun c : E => ⟪v,c⟫) (fun c : E => ⟪w,c⟫) (stdGaussian E) := by
  have hj : HasGaussianLaw (fun c : E => (⟪v,c⟫,⟪w,c⟫)) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map ((innerSL ℝ v).prod (innerSL ℝ w))
  apply hj.indepFun_of_covariance_eq_zero
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  exact hvw

lemma sign_inner_le {v w : E} (hv : ‖v‖=1) (hw : ‖w‖=1) :
    (∫ c : E, signFailure ⟪v,c⟫ ⟪w,c⟫ ∂stdGaussian E) ≤ 2*‖v-w‖ := by
  by_cases hd : 1 ≤ ‖v-w‖
  · have h := integral_mono (signFailure_integrable (μ := stdGaussian E) (X := fun c => ⟪v,c⟫) (Y := fun c => ⟪w,c⟫) (by fun_prop) (by fun_prop))
        (integrable_const (1:ℝ)) (fun c : E => (signFailure_range ⟪v,c⟫ ⟪w,c⟫).2)
    simp only [integral_const,probReal_univ,one_smul] at h
    linarith
  have hd1 : ‖v-w‖ < 1 := lt_of_not_ge hd
  have horth : ⟪v+w,v-w⟫=0 := by
    simp only [inner_add_left,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm w v,hv,hw]
    ring
  have hsum : (1:ℝ) ≤ ‖v+w‖^2 := by
    have h := parallelogram_law_with_norm ℝ v w
    simp only [hv,hw,one_pow] at h
    nlinarith [norm_nonneg (v-w)]
  have hh := independent_small_ball (μ := stdGaussian E)
    (X := fun c : E => ⟪v+w,c⟫) (Y := fun c : E => ⟪v-w,c⟫)
    (by fun_prop) (by fun_prop) (inner_hasGaussianLaw (v-w)).integrable
    (orthogonal_indep horth) (v := ⟨‖v+w‖^2,sq_nonneg _⟩) (by exact_mod_cast hsum) (inner_law _)
  have hi := integral_abs_le_sqrt_sq (inner_hasGaussianLaw (v-w)).memLp_two
  rw [inner_second_moment,Real.sqrt_sq (norm_nonneg _)] at hi
  have hb := integral_mono (signFailure_integrable (μ := stdGaussian E) (X := fun c => ⟪v,c⟫) (Y := fun c => ⟪w,c⟫) (by fun_prop) (by fun_prop))
    (between_integrable (μ := stdGaussian E) (X := fun c => ⟪v+w,c⟫) (Y := fun c => ⟪v-w,c⟫)
      (by fun_prop) (by fun_prop)) (fun c => by
      simpa only [inner_add_left,inner_sub_left] using signFailure_sumdiff_le ⟪v,c⟫ ⟪w,c⟫)
  linarith

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι]

def score (v c : ι → ℝ) : ℝ := ∑ i, v i*c i
abbrev vector (v : ι → ℝ) : EuclideanSpace ℝ ι := WithLp.toLp 2 v

lemma score_inner (v c : ι → ℝ) : score v c=⟪vector v,vector c⟫ := by
  simp [score,PiLp.inner_apply,vector,mul_comm]

lemma toLp_preserving : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ))
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) (stdGaussian (EuclideanSpace ℝ ι)) :=
  ⟨(MeasurableEquiv.toLp 2 (ι → ℝ)).measurable,map_pi_eq_stdGaussian⟩

lemma integral_score_sign (v w : ι → ℝ) :
    (∫ c, signFailure (score v c) (score w c) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ c : EuclideanSpace ℝ ι, signFailure ⟪vector v,c⟫ ⟪vector w,c⟫ ∂stdGaussian (EuclideanSpace ℝ ι) := by
  simpa only [score_inner,MeasurableEquiv.toLp_apply] using toLp_preserving.integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
    (fun c : EuclideanSpace ℝ ι => signFailure ⟪vector v,c⟫ ⟪vector w,c⟫)

lemma sign_score_le {v w : ι → ℝ} (hv : ‖vector v‖=1) (hw : ‖vector w‖=1) :
    (∫ c, signFailure (score v c) (score w c) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤ 2*‖vector v-vector w‖ := by
  rw [integral_score_sign]
  exact sign_inner_le hv hw

lemma signFailure_mul_right {r : ℝ} (hr : 0<r) (x y : ℝ) : signFailure x (r*y)=signFailure x y := by
  simp only [signFailure,mul_nonneg_iff_of_pos_left hr]

lemma signFailure_mul {r : ℝ} (hr : 0<r) (x y : ℝ) : signFailure (r*x) (r*y)=signFailure x y := by
  simp only [signFailure,mul_nonneg_iff_of_pos_left hr]

section Norm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma norm_unit (v : E) (hv : 0<‖v‖) : ‖(‖v‖⁻¹:ℝ) • v‖=1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv),inv_mul_cancel₀ hv.ne']

lemma distance_normalize {u v : E} (hu : ‖u‖=1) (hv : 0<‖v‖) :
    ‖u-(‖v‖⁻¹:ℝ) • v‖ ≤ 2*‖u-v‖ := by
  have he : v-(‖v‖⁻¹:ℝ) • v=(1-‖v‖⁻¹:ℝ) • v := by rw [sub_smul,one_smul]
  have hn : ‖v-(‖v‖⁻¹:ℝ) • v‖=|‖v‖-1| := by
    rw [he,norm_smul,Real.norm_eq_abs]
    calc
      |1-‖v‖⁻¹| *‖v‖ = |(1-‖v‖⁻¹)*‖v‖| := by rw [abs_mul,abs_of_nonneg (norm_nonneg v)]
      _ = |‖v‖-1| := by congr 1; field_simp

  have h := dist_triangle u v ((‖v‖⁻¹:ℝ) • v)
  simp only [dist_eq_norm] at h
  have hb := abs_norm_sub_norm_le v u
  rw [hu,norm_sub_rev v u] at hb
  rw [hn] at h
  linarith
end Norm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
lemma sign_inner_normalize_le {v w : E} (hv : ‖v‖=1) (hw : 0<‖w‖) :
    (∫ c : E, signFailure ⟪v,c⟫ ⟪w,c⟫ ∂stdGaussian E) ≤ 4*‖v-w‖ := by
  have h := sign_inner_le hv (norm_unit w hw)
  simp only [real_inner_smul_left,
    signFailure_mul_right (inv_pos.mpr hw)] at h
  exact h.trans (by have := distance_normalize hv hw; linarith)

lemma sign_inner_common_norm {v w : E} {s : ℝ} (hs : 0<s) (hv : ‖v‖=s) (hw : ‖w‖=s) :
    (∫ c : E, signFailure ⟪v,c⟫ ⟪w,c⟫ ∂stdGaussian E) ≤ 2/s*‖v-w‖ := by
  have hv1 : ‖s⁻¹ • v‖=1 := by simpa only [hv] using norm_unit v (by rw [hv]; exact hs)
  have hw1 : ‖s⁻¹ • w‖=1 := by simpa only [hw] using norm_unit w (by rw [hw]; exact hs)
  have h := sign_inner_le hv1 hw1
  simp only [real_inner_smul_left,signFailure_mul (inv_pos.mpr hs)] at h
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)] at h
  convert h using 1; ring
end MinUncut.GaussianBudget

open scoped BigOperators Topology
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

def evenExp (r : ℕ) (u : ℝ) : ℝ := ∑ j ∈ Finset.range (2*r+1), (-u)^j/(j.factorial:ℝ)

def densityPolynomial (r : ℕ) (v : ℝ) : ℝ := evenExp r (v^2/2)

def error (r : ℕ) (U : ℝ) : ℝ := U^(2*r+1)/((2*r+1).factorial:ℝ)

lemma taylor_exp (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    taylorWithinEval Real.exp n (Set.uIcc 0 x) 0 x =
      ∑ j ∈ Finset.range (n+1), x^j/(j.factorial:ℝ) := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.symm)
    Real.contDiff_exp.contDiffAt (by simp)]
  simp [iteratedDeriv_eq_iterate,Real.iter_deriv_exp,div_eq_mul_inv,mul_comm]

lemma evenExp_error {u : ℝ} (hu : 0 ≤ u) (r : ℕ) :
    0 ≤ evenExp r u-Real.exp (-u) ∧
      evenExp r u-Real.exp (-u) ≤ error r u := by
  rcases hu.eq_or_lt with he|hu
  · subst u
    simp [evenExp,error,Finset.sum_range_succ']
  have hx : (0:ℝ) ≠ -u := by linarith
  obtain ⟨z,hz,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.exp) (n := 2*r)
    hx (Real.contDiff_exp.contDiffOn)
  rw [taylor_exp (2*r) hx.symm] at he
  simp only [iteratedDeriv_eq_iterate,Real.iter_deriv_exp,sub_zero] at he
  have hz0 : z < 0 := by
    have hh := hz
    rw [Set.uIoo_of_ge (by linarith : -u ≤ 0)] at hh
    exact hh.2
  have hpow : (-u)^(2*r+1) = -(u^(2*r+1)) := by
    rw [pow_succ,pow_mul,neg_sq,pow_succ]
    ring
  rw [hpow] at he
  have heq : evenExp r u-Real.exp (-u)=Real.exp z*error r u := by
    dsimp [evenExp,error,Finset.sum_range_succ']
    linear_combination -he
  rw [heq]
  have herror : 0 ≤ error r u := by unfold error; positivity
  exact ⟨mul_nonneg (Real.exp_nonneg _) herror,
    by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr hz0.le) herror)⟩

lemma density_bounds {T v : ℝ} (hT : 0 ≤ T) (hv : |v| ≤ T) (r : ℕ) :
    0 ≤ densityPolynomial r v-Real.exp (-v^2/2) ∧
      densityPolynomial r v-Real.exp (-v^2/2) ≤ error r (T^2/2) := by
  have hu : 0 ≤ v^2/2 := by positivity
  have hb : v^2/2 ≤ T^2/2 := by
    have hh := (sq_le_sq₀ (abs_nonneg v) hT).mpr hv
    rw [sq_abs] at hh
    linarith
  obtain ⟨h0,h1⟩ := evenExp_error hu r
  have he : error r (v^2/2) ≤ error r (T^2/2) := by
    unfold error
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hu hb _) (by positivity)
  simpa only [densityPolynomial,neg_div] using ⟨h0,h1.trans he⟩

lemma density_positive (r : ℕ) (v : ℝ) : 0 < densityPolynomial r v := by
  have h := (evenExp_error (by positivity : 0 ≤ v^2/2) r).1
  have := Real.exp_pos (-(v^2/2))
  dsimp [densityPolynomial]
  linarith

lemma exists_error {U ε : ℝ} (hε : 0 < ε) : ∃ r : ℕ, error r U < ε := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop U
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (h.eventually_lt_const hε)
  refine ⟨N,?_⟩
  exact hN (2*N+1) (by omega)

open scoped BigOperators
open MeasureTheory

def coefficient (j : ℕ) : ℚ := (-1)^j/((2:ℚ)^j*j.factorial)
def primitive (r : ℕ) (v : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (2*r+1), coefficient j*v^(2*j+1)/(2*j+1)
def qIntegral (r : ℕ) (a b : ℚ) : ℚ := primitive r b-primitive r a

lemma density_sum (r : ℕ) (v : ℝ) :
    densityPolynomial r v=∑ j ∈ Finset.range (2*r+1), (coefficient j:ℝ)*v^(2*j) := by
  unfold densityPolynomial evenExp
  apply Finset.sum_congr rfl
  intro j _
  unfold coefficient
  push_cast
  rw [neg_eq_neg_one_mul,mul_pow,div_pow,pow_mul]
  ring

lemma continuous_density (r : ℕ) : Continuous (densityPolynomial r) := by
  simp_rw [funext (density_sum r)]
  fun_prop

lemma qIntegral_cast (r : ℕ) (a b : ℚ) :
    (qIntegral r a b:ℝ)=∫ v in (a:ℝ)..(b:ℝ), densityPolynomial r v := by
  simp_rw [density_sum]
  rw [intervalIntegral.integral_finsetSum (f := fun (j : ℕ) (v : ℝ) => (coefficient j:ℝ)*v^(2*j))
    (fun j _ => (show Continuous (fun v : ℝ => (coefficient j:ℝ)*v^(2*j)) by fun_prop).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul,integral_pow]
  unfold qIntegral primitive
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma qIntegral_pos (r : ℕ) {a b : ℚ} (hab : a < b) : 0 < qIntegral r a b := by
  apply (Rat.cast_pos (K := ℝ)).mp
  rw [qIntegral_cast]
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  exact intervalIntegral.integral_pos hab' (continuous_density r).continuousOn
    (fun v _ => (density_positive r v).le) ⟨a,⟨le_rfl,hab'.le⟩,density_positive r a⟩

def endpoint (T : ℚ) (L i : ℕ) : ℚ := -T+2*T*i/L
def midpoint (T : ℚ) (L i : ℕ) : ℚ := (endpoint T L i+endpoint T L (i+1))/2

def cellWeight (r : ℕ) (T : ℚ) (L : ℕ) (i : Fin L) : ℚ :=
  qIntegral r (endpoint T L i) (endpoint T L (i+1))/qIntegral r (-T) T

lemma endpoint_zero (T : ℚ) (L : ℕ) : endpoint T L 0 = -T := by simp [endpoint]
lemma endpoint_end (T : ℚ) {L : ℕ} (hL : 0 < L) : endpoint T L L=T := by
  have hh : (L:ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold endpoint
  field_simp
  ring

lemma endpoint_lt {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (i : ℕ) :
    endpoint T L i < endpoint T L (i+1) := by
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  unfold endpoint
  simp only [add_lt_add_iff_left,div_lt_div_iff_of_pos_right hL']
  push_cast
  nlinarith

lemma cellWeight_pos {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (r : ℕ) (i : Fin L) :
    0 < cellWeight r T L i := by
  exact div_pos (qIntegral_pos r (endpoint_lt hT hL i)) (qIntegral_pos r (by linarith))

lemma sum_cellWeight {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (r : ℕ) :
    ∑ i : Fin L, cellWeight r T L i=1 := by
  have hden : qIntegral r (-T) T ≠ 0 := (qIntegral_pos r (by linarith)).ne'
  unfold cellWeight
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => qIntegral r (endpoint T L i) (endpoint T L (i+1)))]
  have he : (∑ i ∈ Finset.range L, qIntegral r (endpoint T L i) (endpoint T L (i+1)))=
      qIntegral r (-T) T := by
    unfold qIntegral
    rw [Finset.sum_range_sub (fun i => primitive r (endpoint T L i)),endpoint_zero,endpoint_end T hL]
  rw [he,div_self hden]

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

lemma endpoint_mono {T : ℚ} (hT : 0 ≤ T) {L i j : ℕ} (hij : i ≤ j) :
    endpoint T L i ≤ endpoint T L j := by
  unfold endpoint
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by positivity)

def cell (T : ℚ) (L : ℕ) (i : Fin L) : Set ℝ :=
  Ioc (endpoint T L i) (endpoint T L (i+1))

lemma cell_subset {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) (i : Fin L) :
    cell T L i ⊆ Ioc (-(T:ℝ)) T := by
  apply Ioc_subset_Ioc
  · have hh := endpoint_mono hT (Nat.zero_le i.val) (L := L)
    rw [endpoint_zero] at hh
    exact_mod_cast hh
  · have hh := endpoint_mono hT (Nat.succ_le_of_lt i.isLt) (L := L)
    rw [endpoint_end T hL] at hh
    exact_mod_cast hh

lemma exists_cell {T : ℚ} {L : ℕ} (hL : 0 < L) {x : ℝ} (hx : x ∈ Ioc (-(T:ℝ)) T) :
    ∃ i : Fin L, x ∈ cell T L i := by
  have hh := Ioc_subset_biUnion_Ioc L (fun i => (endpoint T L i:ℝ))
  rw [endpoint_zero,endpoint_end T hL] at hh
  have hx' := hh (by simpa only [Rat.cast_neg] using hx)
  obtain ⟨i,hi,hx'⟩ := Set.mem_iUnion₂.mp hx'
  exact ⟨⟨i,Finset.mem_range.mp hi⟩,hx'⟩

lemma disjoint_cells {T : ℚ} (hT : 0 ≤ T) {L : ℕ} {i j : Fin L} (hij : i ≠ j) :
    Disjoint (cell T L i) (cell T L j) := by
  rcases lt_or_gt_of_ne hij with h|h
  · apply Set.Ioc_disjoint_Ioc_of_le
    exact_mod_cast endpoint_mono hT (show i.val+1 ≤ j.val by exact Nat.succ_le_of_lt h) (L := L)
  · apply Disjoint.symm
    apply Set.Ioc_disjoint_Ioc_of_le
    exact_mod_cast endpoint_mono hT (show j.val+1 ≤ i.val by exact Nat.succ_le_of_lt h) (L := L)

lemma midpoint_distance {T : ℚ} {L : ℕ} (i : Fin L) {x : ℝ} (hx : x ∈ cell T L i) :
    |x-(midpoint T L i:ℝ)| ≤ (T:ℝ)/L := by
  have he : (endpoint T L (i.val+1):ℝ)-(endpoint T L i.val:ℝ)=2*((T:ℝ)/L) := by
    unfold endpoint
    push_cast
    ring
  have hm : (midpoint T L i:ℝ)=((endpoint T L i:ℝ)+(endpoint T L (i.val+1):ℝ))/2 := by
    unfold midpoint
    push_cast
    rfl
  rw [hm]
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩

variable {ι : Type*} [Fintype ι]
def cube (T : ℚ) : Set (ι → ℝ) := Set.pi Set.univ (fun _ => Ioc (-(T:ℝ)) T)
def cubeCell (T : ℚ) (L : ℕ) (j : ι → Fin L) : Set (ι → ℝ) := Set.pi Set.univ (fun i => cell T L (j i))
def gridPoint (T : ℚ) (L : ℕ) (j : ι → Fin L) : ι → ℝ := fun i => midpoint T L (j i)

lemma cubeCell_measurable (T : ℚ) (L : ℕ) (j : ι → Fin L) : MeasurableSet (cubeCell T L j) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioc)

lemma cube_measurable (T : ℚ) : MeasurableSet (cube (ι := ι) T) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioc)

omit [Fintype ι] in
lemma cubeCell_subset {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) (j : ι → Fin L) :
    cubeCell T L j ⊆ cube T := by
  intro x hx i hi
  exact cell_subset hT hL (j i) (hx i hi)

omit [Fintype ι] in
lemma cube_union {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) :
    (⋃ j : ι → Fin L, cubeCell T L j)=cube T := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (cubeCell_subset hT hL)
  · intro x hx
    have hh : ∀ i : ι, ∃ j : Fin L, x i ∈ cell T L j := fun i => exists_cell hL (hx i (by simp))
    choose j hj using hh
    exact Set.mem_iUnion.mpr ⟨j,fun i _ => hj i⟩

omit [Fintype ι] in
lemma cubeCell_disjoint {T : ℚ} (hT : 0 ≤ T) {L : ℕ} {j k : ι → Fin L} (hjk : j ≠ k) :
    Disjoint (cubeCell T L j) (cubeCell T L k) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hjk
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (disjoint_cells hT hi) (hx i (by simp)) (hy i (by simp))

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

def gridStep (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ j, (cubeCell T L j).indicator (fun _ => F j) x

lemma gridStep_of_mem {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (F : (ι → Fin L) → ℝ)
    {j : ι → Fin L} {x : ι → ℝ} (hx : x ∈ cubeCell T L j) :
    gridStep T L F x=F j := by
  unfold gridStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro k _ hk
    exact Set.indicator_of_notMem (fun hkx =>
      Set.disjoint_left.mp (cubeCell_disjoint hT hk) hkx hx) _
  · simp

lemma gridStep_of_notMem {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (ι → Fin L) → ℝ) {x : ι → ℝ} (hx : x ∉ cube T) : gridStep T L F x=0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact Set.indicator_of_notMem (fun hj => hx (cubeCell_subset hT hL j hj)) _

lemma gridStep_range {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (ι → Fin L) → ℝ) (hF : ∀ j, 0 ≤ F j ∧ F j ≤ 1) (x : ι → ℝ) :
    0 ≤ gridStep T L F x ∧ gridStep T L F x ≤ 1 := by
  by_cases hx : x ∈ cube T
  · rw [← cube_union hT hL] at hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    simpa only [gridStep_of_mem hT F hj] using hF j
  · rw [gridStep_of_notMem hT hL F hx]; norm_num

lemma gridStep_integrable {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) : Integrable (gridStep T L F) μ := by
  exact integrable_finsetSum _ (fun j _ => (integrable_const (F j)).indicator (cubeCell_measurable T L j))

lemma integral_gridStep {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) :
    (∫ x, gridStep T L F x ∂μ)=∑ j, μ.real (cubeCell T L j)*F j := by
  unfold gridStep
  rw [integral_finsetSum _ (fun j _ => (integrable_const (F j)).indicator (cubeCell_measurable T L j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (cubeCell_measurable T L j),setIntegral_const,smul_eq_mul]

lemma setIntegral_gridStep {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L) (F : (ι → Fin L) → ℝ) :
    (∫ x in cube T, gridStep T L F x ∂μ)=∑ j, μ.real (cubeCell T L j)*F j := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => gridStep_of_notMem hT hL F hx)]
  exact integral_gridStep T L F

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]

abbrev gaussianLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

lemma coordinate_sq_integrable (i : ι) : Integrable (fun x : ι → ℝ => x i^2) (gaussianLaw ι) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).integrable_sq
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable h

lemma coordinate_second_moment (i : ι) : (∫ x : ι → ℝ, x i^2 ∂gaussianLaw ι)=1 := by
  have hp := measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  have h : (∫ x : ℝ, x^2 ∂gaussianReal 0 1)=1 := by
    have hh := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    change Var[id; gaussianReal 0 1] = (1:ℝ) at hh
    rw [variance_eq_integral measurable_id.aemeasurable] at hh
    simpa only [id_eq,integral_id_gaussianReal,sub_zero,NNReal.coe_one] using hh
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable (by fun_prop)] at h
  exact h

lemma gaussian_cube_tail {T : ℚ} (hT : 0 < T) :
    (gaussianLaw ι).real (cube T)ᶜ ≤ (Fintype.card ι:ℝ)/(T:ℝ)^2 := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  let F : (ι → ℝ) → ℝ := (cube (ι := ι) T)ᶜ.indicator (fun _ => 1)
  have hi : Integrable F (gaussianLaw ι) := (integrable_const (1:ℝ)).indicator (cube_measurable T).compl
  have hacc : Integrable (fun x : ι → ℝ => (∑ i, x i^2)/(T:ℝ)^2) (gaussianLaw ι) :=
    (integrable_finsetSum _ (fun i _ => coordinate_sq_integrable i)).div_const _
  have hpoint (x : ι → ℝ) : F x ≤ (∑ i, x i^2)/(T:ℝ)^2 := by
    by_cases hx : x ∈ cube (ι := ι) T
    · simp only [F,Set.indicator_of_notMem (show x ∉ (cube T)ᶜ from fun hh => hh hx)]
      positivity
    · rw [show F x=1 by exact Set.indicator_of_mem hx _]
      apply (le_div_iff₀ (sq_pos_of_pos hT')).mpr
      obtain ⟨i,hi⟩ : ∃ i : ι, ¬ (-(T:ℝ)<x i ∧ x i ≤ T) := by
        simpa only [cube,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Ioc,not_forall] using hx
      have hs : (T:ℝ)^2 ≤ x i^2 := by
        rcases not_and_or.mp hi with h|h
        · have := le_of_not_gt h; nlinarith
        · have := lt_of_not_ge h; nlinarith
      have hb := Finset.single_le_sum (s := Finset.univ) (a := i) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      simpa only [one_mul] using hs.trans hb
  have hh := integral_mono hi hacc hpoint
  have hleft : (∫ x, F x ∂gaussianLaw ι)=(gaussianLaw ι).real (cube T)ᶜ := by
    change (∫ x, (cube (ι := ι) T)ᶜ.indicator (fun _ => (1:ℝ)) x ∂gaussianLaw ι)=_
    rw [integral_indicator (cube_measurable T).compl,setIntegral_const,smul_eq_mul,mul_one]
  have hright : (∫ x : ι → ℝ, (∑ i, x i^2)/(T:ℝ)^2 ∂gaussianLaw ι)=(Fintype.card ι:ℝ)/(T:ℝ)^2 := by
    rw [integral_div,integral_finsetSum _ (fun i _ => coordinate_sq_integrable i)]
    simp only [coordinate_second_moment,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  simpa only [hleft,hright] using hh

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

def thresholdBit (x : ℝ) : Bool := if 0 ≤ x then true else false

def thresholdTable (v : S → ι → ℝ) (x : ι → ℝ) : S → Bool :=
  fun s => thresholdBit (score (v s) x)

lemma thresholdBit_measurable : Measurable thresholdBit :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

omit [Fintype S] in
lemma thresholdTable_measurable (v : S → ι → ℝ) : Measurable (thresholdTable v) := by
  apply Measurable.of_eval
  intro s
  exact thresholdBit_measurable.comp (by unfold score; fun_prop)

lemma tableTest_integrable (v : S → ι → ℝ) (F : (S → Bool) → ℝ)
    (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    Integrable (fun x => F (thresholdTable v x)) (gaussianLaw ι) := by
  apply Integrable.of_bound ((measurable_of_countable F).comp (thresholdTable_measurable v)).aestronglyMeasurable 1
  filter_upwards [] with x
  simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (hF _).1] using (hF (thresholdTable v x)).2

lemma score_law (v : ι → ℝ) : (gaussianLaw ι).map (score v)=
    gaussianReal 0 ⟨‖vector v‖^2,sq_nonneg _⟩ := by
  rw [← inner_law (vector v),← toLp_preserving.map_eq]
  rw [Measure.map_map (by fun_prop) toLp_preserving.measurable]
  congr 1
  ext x
  exact score_inner v x

lemma score_small_ball {v : ι → ℝ} (hv : 1 ≤ ‖vector v‖^2) {r : ℝ} (hr : 0 ≤ r) :
    (gaussianLaw ι).real {x | |score v x| ≤ r} ≤ 2*r := by
  have hh := small_ball (by exact_mod_cast hv : (1:ℝ≥0) ≤ ⟨‖vector v‖^2,sq_nonneg _⟩) hr
  rw [← score_law v,Measure.real,Measure.map_apply (by unfold score; fun_prop)
    (measurableSet_le (by fun_prop) measurable_const)] at hh
  exact hh

lemma score_grid_distance (v : ι → ℝ) {T : ℚ} {L : ℕ} {j : ι → Fin L}
    {x : ι → ℝ} (hx : x ∈ cubeCell T L j) :
    |score v x-score v (gridPoint T L j)| ≤ (∑ i, |v i|)*((T:ℝ)/L) := by
  unfold score
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |v i*x i-v i*gridPoint T L j i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| *((T:ℝ)/L) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (midpoint_distance (j i) (hx i (by simp))) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma threshold_change_small {a b r : ℝ} (hr : |a-b| ≤ r)
    (hab : thresholdBit a ≠ thresholdBit b) : |a| ≤ r := by
  unfold thresholdBit at hab
  split_ifs at hab with ha hb hb
  · exact False.elim (hab rfl)
  · rw [abs_of_nonneg ha] at ⊢
    have hh : b < 0 := lt_of_not_ge hb
    have := (abs_le.mp hr).2
    linarith
  · rw [abs_of_neg (lt_of_not_ge ha)]
    have := (abs_le.mp hr).1
    linarith
  · exact False.elim (hab rfl)

lemma tableTest_rounding_pointwise (v : S → ι → ℝ) {A : ℝ}
    (hA : ∀ s, (∑ i, |v s i|) ≤ A) {T : ℚ} (hT : 0 ≤ T) {L : ℕ} (hL : 0 < L)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1)
    {x : ι → ℝ} (hx : x ∈ cube T) :
    |F (thresholdTable v x)-gridStep T L (fun j => F (thresholdTable v (gridPoint T L j))) x| ≤
      ∑ s, {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) x := by
  rw [← cube_union hT hL] at hx
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
  rw [gridStep_of_mem hT _ hj]
  by_cases he : thresholdTable v x=thresholdTable v (gridPoint T L j)
  · rw [he,sub_self,abs_zero]
    exact Finset.sum_nonneg (fun s _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)
  · obtain ⟨s,hs⟩ := Function.ne_iff.mp he
    have hdist : |score (v s) x-score (v s) (gridPoint T L j)| ≤ A*((T:ℝ)/L) :=
      (score_grid_distance (v s) hj).trans (mul_le_mul_of_nonneg_right (hA s) (by positivity))
    have hb := threshold_change_small hdist hs
    have hone : {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) x=1 :=
      Set.indicator_of_mem (show x ∈ {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)} from hb) _
    have hsum := Finset.single_le_sum (s := Finset.univ) (a := s)
      (f := fun s => {x : ι → ℝ | |score (v s) x| ≤ A*((T:ℝ)/L)}.indicator (fun _ => (1:ℝ)) x)
      (fun _ _ => Set.indicator_nonneg (fun _ _ => by norm_num) x) (Finset.mem_univ s)
    rw [hone] at hsum
    exact (abs_le.mpr ⟨by linarith [(hF (thresholdTable v x)).1,(hF (thresholdTable v (gridPoint T L j))).2],
      by linarith [(hF (thresholdTable v x)).2,(hF (thresholdTable v (gridPoint T L j))).1]⟩).trans hsum

end MinUncut.FiniteGaussian

end

end OAI
