import Mathlib
import OAI.Probability.Ballisticity.Estimates.RecordIndexTime

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def integerMedian (μ : Measure ℤ) [IsProbabilityMeasure μ] : ℤ :=
  (exists_integer_median μ).choose

lemma integerMedian_spec (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    (1/2 : ℝ≥0∞) ≤ μ (Set.Iic (integerMedian μ)) ∧
    (1/2 : ℝ≥0∞) ≤ μ (Set.Ici (integerMedian μ)) :=
  (exists_integer_median μ).choose_spec

lemma median_family_symmetrization {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (b : ι → ℝ)
    (hb : ∀ i, (1/2 : ℝ≥0∞) ≤ μ {x | f i x ≤ b i} ∧
      (1/2 : ℝ≥0∞) ≤ μ {x | b i ≤ f i x}) (s : Set ι) (z : ℝ) :
    (1/2 : ℝ≥0∞) * μ {x | ∃ i ∈ s, z < |f i x-b i|} ≤
      μ.prod μ {P | ∃ i ∈ s, z < |f i P.1-f i P.2|} := by
  classical
  let A : Set Ω := {x | ∃ i ∈ s, z < |f i x-b i|}
  let E : Set (Ω × Ω) := {P | ∃ i ∈ s, z < |f i P.1-f i P.2|}
  have hA : MeasurableSet A := by
    simp only [A,Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const ((hf i).sub_const (b i)).abs)
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const
        (((hf i).comp measurable_fst).sub ((hf i).comp measurable_snd)).abs)
  change (1/2 : ℝ≥0∞) * μ A ≤ μ.prod μ E
  rw [Measure.prod_apply hE]
  calc
    _ = ∫⁻ x, A.indicator (fun _ => (1/2 : ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator hA,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        obtain ⟨i,hi,hlarge⟩ := hx
        rcases (lt_abs.mp hlarge) with hright | hleft
        · apply (hb i).1.trans (measure_mono ?_)
          intro y hy
          change f i y ≤ b i at hy
          refine ⟨i,hi,?_⟩
          exact lt_of_lt_of_le (by linarith : z < f i x-f i y) (le_abs_self _)
        · apply (hb i).2.trans (measure_mono ?_)
          intro y hy
          change b i ≤ f i y at hy
          refine ⟨i,hi,?_⟩
          exact lt_of_lt_of_le (by linarith : z < -(f i x-f i y)) (neg_le_abs _)
      · rw [Set.indicator_of_notMem hx]
        exact bot_le

def signedIntegerCoordinate {d : ℕ} (e : Direction d) (x : Lattice d) : ℤ :=
  if e.2 then x e.1 else -x e.1

lemma signedIntegerCoordinate_cast {d : ℕ} (e : Direction d) (x : Lattice d) :
    (signedIntegerCoordinate e x : ℝ) = signedCoordinate e x := by
  simp only [signedIntegerCoordinate,signedCoordinate]
  split <;> simp

noncomputable def recordMedian {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (e : Direction d) (r : ℕ) : ℤ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let f : Path d → ℤ := fun X => signedIntegerCoordinate e (recordIndexPosition ℓ r X)
  have hf : Measurable f := (measurable_of_countable (signedIntegerCoordinate e)).comp (measurable_recordIndexPosition ℓ r)
  let : IsProbabilityMeasure ((conditionedLaw ν ℓ).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  exact integerMedian ((conditionedLaw ν ℓ).map f)

lemma recordMedian_spec {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (e : Direction d) (r : ℕ) :
    (1/2 : ℝ≥0∞) ≤ conditionedLaw ν ℓ
      {X | signedCoordinate e (recordIndexPosition ℓ r X) ≤ (recordMedian ν ℓ hp e r : ℝ)} ∧
    (1/2 : ℝ≥0∞) ≤ conditionedLaw ν ℓ
      {X | (recordMedian ν ℓ hp e r : ℝ) ≤ signedCoordinate e (recordIndexPosition ℓ r X)} := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let f : Path d → ℤ := fun X => signedIntegerCoordinate e (recordIndexPosition ℓ r X)
  have hf : Measurable f := (measurable_of_countable (signedIntegerCoordinate e)).comp (measurable_recordIndexPosition ℓ r)
  let : IsProbabilityMeasure ((conditionedLaw ν ℓ).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have h := integerMedian_spec ((conditionedLaw ν ℓ).map f)
  rw [Measure.map_apply hf measurableSet_Iic,Measure.map_apply hf measurableSet_Ici] at h
  have he (X : Path d) : signedCoordinate e (recordIndexPosition ℓ r X) = (f X : ℝ) :=
    (signedIntegerCoordinate_cast e _).symm
  simp only [he,Int.cast_le] at ⊢
  exact h

lemma conditioned_firstHit_median_maximum {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (H : ℕ) (z : ℝ) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * (1/2 : ℝ≥0∞) * conditionedLaw ν ℓ
      {X | ∃ r, 0 < r ∧ r ≤ H ∧
        z < |signedCoordinate e (recordIndexPosition ℓ r X) -
          (recordMedian ν ℓ (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) e r : ℝ)|} ≤
    independentConditionedPairLaw ν ℓ
      {P | z < partialSumMax (fun n => commonIncrementProcess ℓ e n P) H} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  have hs := median_family_symmetrization (conditionedLaw ν ℓ)
    (fun r X => signedCoordinate e (recordIndexPosition ℓ r X))
    (fun r => (measurable_of_countable (signedCoordinate e)).comp (measurable_recordIndexPosition ℓ r))
    (fun r => (recordMedian ν ℓ hp e r : ℝ)) (recordMedian_spec ν ℓ hp e)
    {r | 0 < r ∧ r ≤ H} z
  simp only [Set.mem_ofPred_eq,and_assoc] at hs
  rw [mul_assoc]
  exact (mul_le_mul_right hs _).trans
    (independent_firstHit_pair_maximum ν ℓ htrans height hproj hstep e H z)

def IsGaussianSequence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℕ → ℝ) : Prop :=
  Tendsto r atTop atTop ∧ ∀ a : ℝ, 0 < a →
    Tendsto (fun i => fluctuationScale μ S (r i) * μ.real {x | a*r i < |S x|})
      atTop (𝓝 0)

lemma one_sub_cos_sinc (x : ℝ) :
    1-Real.cos x = x^2/2*(Real.sinc (x/2))^2 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero (div_ne_zero hx (by norm_num))]
    have hc := Real.cos_two_mul (x/2)
    have hs := Real.sin_sq_add_cos_sq (x/2)
    have he : 2*(x/2) = x := by ring
    rw [he] at hc
    field_simp
    nlinarith

lemma cosine_quadratic_local (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ y : ℝ, |y| ≤ δ →
      |(1-Real.cos (t*y)) - (t^2/2)*y^2| ≤ ε*y^2 := by
  let c : ℝ → ℝ := fun y => t^2/2*((Real.sinc (t*y/2))^2-1)
  have hc : Continuous c := by fun_prop
  have hc0 : c 0 = 0 := by simp [c]
  obtain ⟨δ,hδ,hd⟩ := (Metric.continuousAt_iff.mp hc.continuousAt) ε hε
  refine ⟨min (δ/2) 1,lt_min (by positivity) zero_lt_one,min_le_right ..,?_⟩
  intro y hy
  have hyd : dist y 0 < δ := by
    rw [Real.dist_eq,sub_zero]
    exact lt_of_le_of_lt (hy.trans (min_le_left ..)) (by linarith)
  have hcy : |c y| < ε := by simpa [Real.dist_eq,hc0] using hd hyd
  have he : (1-Real.cos (t*y)) - (t^2/2)*y^2 = c y*y^2 := by
    rw [one_sub_cos_sinc]
    dsimp [c]
    ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg y)]
  exact mul_le_mul_of_nonneg_right hcy.le (sq_nonneg y)

lemma truncatedVariance_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) {r : ℝ} (hr : 0 < r) :
    truncatedVariance μ (fun x => S x/r) 1 = truncatedVariance μ S r / r^2 := by
  unfold truncatedVariance
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [one_pow,div_pow,← min_div_div_right (le_of_lt (sq_pos_of_pos hr)),div_self (pow_ne_zero 2 (ne_of_gt hr))]

lemma gaussian_quadratic_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : IsGaussianSequence μ S r)
    (g : ℝ → ℝ) (hg : Measurable g) (c C : ℝ) (hC : ∀ y, |g y| ≤ C)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ y, |y| ≤ δ → |g y-c*y^2| ≤ ε*y^2) :
    Tendsto (fun i => fluctuationScale μ S (r i) * ∫ x, g (S x/r i) ∂μ)
      atTop (𝓝 c) := by
  have hC0 : 0 ≤ C := (abs_nonneg (g 0)).trans (hC 0)
  have hIg (i : ℕ) : Integrable (fun x => g (S x/r i)) μ :=
    (integrable_const C).mono' ((hg.comp (hS.div_const _)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC (S x/r i))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδ1,hlocal⟩ := hc (ε/2) (by positivity)
  have htail : Tendsto (fun i => (C+|c|) *
      (fluctuationScale μ S (r i) * μ.real {x | δ*r i < |S x|})) atTop (𝓝 0) := by
    simpa using (hr.2 δ hδ).const_mul (C+|c|)
  have ht := (tendsto_order.mp htail).2 (ε/2) (by positivity)
  filter_upwards [hr.1.eventually (eventually_gt_atTop (0:ℝ)),ht] with i hri hti
  let Y : Ω → ℝ := fun x => S x/r i
  let A : Set Ω := {x | δ*r i < |S x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hS.abs
  have hY : Measurable Y := hS.div_const _
  have hmt : Integrable (fun x => min ((Y x)^2) 1) μ := by
    simpa using integrable_truncated_square μ Y hY 1
  have hE : ∀ x, |g (Y x)-c*min ((Y x)^2) 1| ≤
      (ε/2)*min ((Y x)^2) 1 + A.indicator (fun _ => C+|c|) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hm0 : 0 ≤ min ((Y x)^2) 1 := le_min (sq_nonneg _) zero_le_one
      have hm1 : min ((Y x)^2) 1 ≤ 1 := min_le_right ..
      have hb := (abs_sub (g (Y x)) (c*min ((Y x)^2) 1)).trans
        (add_le_add (hC (Y x)) (le_of_eq (abs_mul c _)))
      rw [abs_of_nonneg hm0] at hb
      nlinarith [abs_nonneg c]
    · rw [Set.indicator_of_notMem hx,add_zero]
      have hxy : |Y x| ≤ δ := by
        rw [show Y x = S x/r i from rfl,abs_div,abs_of_pos hri,div_le_iff₀ hri]
        exact le_of_not_gt hx
      have hx1 : (Y x)^2 ≤ 1 := by nlinarith [sq_abs (Y x),abs_nonneg (Y x)]
      rw [min_eq_left hx1]
      exact hlocal _ hxy
  have hInt : |(∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1| ≤
      ε/2*truncatedVariance μ Y 1 + (C+|c|)*μ.real A := by
    simp only [truncatedVariance,one_pow]
    rw [← integral_const_mul,← integral_sub (hIg i) (hmt.const_mul c)]
    calc
      _ ≤ ∫ x, |g (Y x)-c*min ((Y x)^2) 1| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (ε/2)*min ((Y x)^2) 1 + A.indicator (fun _ => C+|c|) x ∂μ :=
        integral_mono ((hIg i).sub (hmt.const_mul c)).abs
          ((hmt.const_mul (ε/2)).add ((integrable_const (C+|c|)).indicator hA)) hE
      _ = _ := by
        rw [integral_add (hmt.const_mul (ε/2)) ((integrable_const (C+|c|)).indicator hA),
          integral_const_mul,integral_indicator hA,integral_const]
        simp [smul_eq_mul,mul_comm,Measure.real]
  have hmpos := truncatedVariance_pos μ S hS hne hri
  have hnpos : 0 < fluctuationScale μ S (r i) := div_pos (sq_pos_of_pos hri) hmpos
  have hnorm : fluctuationScale μ S (r i)*truncatedVariance μ Y 1 = 1 := by
    rw [show Y = (fun x => S x/r i) from rfl,truncatedVariance_div μ S hri,fluctuationScale]
    field_simp
  have hbound := mul_le_mul_of_nonneg_left hInt hnpos.le
  rw [Real.dist_eq]
  have hrew : fluctuationScale μ S (r i)*( (∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1) =
      fluctuationScale μ S (r i)*(∫ x, g (Y x) ∂μ)-c := by
    rw [mul_sub]
    congr 1
    calc
      _ = c*(fluctuationScale μ S (r i)*truncatedVariance μ Y 1) := by ring
      _ = c := by rw [hnorm,mul_one]
  have hab : |fluctuationScale μ S (r i)*( (∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1)| =
      fluctuationScale μ S (r i)*|(∫ x, g (Y x) ∂μ)-c*truncatedVariance μ Y 1| := by
    rw [abs_mul,abs_of_pos hnpos]
  rw [← hab,hrew] at hbound
  have hrw : fluctuationScale μ S (r i) *
      (ε/2*truncatedVariance μ Y 1 + (C+|c|)*μ.real A) =
      ε/2+(C+|c|)*(fluctuationScale μ S (r i)*μ.real A) := by
    calc
      _ = ε/2*(fluctuationScale μ S (r i)*truncatedVariance μ Y 1) +
        (C+|c|)*(fluctuationScale μ S (r i)*μ.real A) := by ring
      _ = _ := by rw [hnorm,mul_one]
  rw [hrw] at hbound
  exact hbound.trans_lt (by linarith)

lemma gaussian_cosine_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : IsGaussianSequence μ S r) (t : ℝ) :
    Tendsto (fun i => fluctuationScale μ S (r i) * ∫ x, 1-Real.cos (t*(S x/r i)) ∂μ)
      atTop (𝓝 (t^2/2)) := by
  apply gaussian_quadratic_integral μ S hS hne r hr
    (fun y => 1-Real.cos (t*y)) (by fun_prop) (t^2/2) 2
  · intro y
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos (t*y)]
  · exact fun ε hε => cosine_quadratic_local t hε

lemma symmetric_sine_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (hsym : IdentDistrib S (fun x => -S x) μ μ) (t : ℝ) :
    (∫ x, Real.sin (t*S x) ∂μ) = 0 := by
  have he := (hsym.comp (u := fun y : ℝ => Real.sin (t*y)) (by fun_prop)).integral_eq
  simp only [Function.comp_def,mul_neg,Real.sin_neg,integral_neg] at he
  linarith

lemma symmetric_charFun_cosine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hsym : IdentDistrib S (fun x => -S x) μ μ) (t : ℝ) :
    charFun (μ.map S) t = ((∫ x, Real.cos (t*S x) ∂μ : ℝ) : ℂ) := by
  have hI : Integrable (fun x => Complex.exp ((t*S x : ℝ)*Complex.I)) μ := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact Eventually.of_forall fun x => (Complex.norm_exp_ofReal_mul_I (t*S x)).le
  rw [charFun_apply_real,integral_map hS.aemeasurable (by fun_prop)]
  simp only [← Complex.ofReal_mul]
  apply Complex.ext
  · simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using (integral_re hI).symm
  · have he := (integral_im hI).symm
    simpa only [RCLike.im_to_complex, Complex.exp_ofReal_mul_I, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, add_zero, zero_add,
      symmetric_sine_integral μ S hsym t] using he

lemma gaussian_cosine_drift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : IsGaussianSequence μ S r) (t : ℝ) :
    Tendsto (fun i => fluctuationScale μ S (r i) *
      ((∫ x, Real.cos (t*(S x/r i)) ∂μ)-1)) atTop (𝓝 (-(t^2/2))) := by
  have hcos (i : ℕ) : Integrable (fun x => Real.cos (t*(S x/r i))) μ :=
    (integrable_const (1:ℝ)).mono' (by fun_prop)
      (Eventually.of_forall fun _ => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  convert (gaussian_cosine_limit μ S hS hne r hr t).neg using 1
  ext i
  rw [integral_sub (integrable_const 1) (hcos i),integral_const]
  simp only [probReal_univ,one_smul]
  ring

lemma tendsto_pow_variable_of_drift {a : ℕ → ℝ} {k : ℕ → ℕ} {c : ℝ}
    (ha : Tendsto a atTop (𝓝 1))
    (hd : Tendsto (fun i => (k i : ℝ)*(a i-1)) atTop (𝓝 c)) :
    Tendsto (fun i => (a i)^(k i)) atTop (𝓝 (Real.exp c)) := by
  have hds : Tendsto (fun i => dslope Real.log 1 (a i)) atTop (𝓝 1) := by
    have h := (continuousAt_dslope_same.mpr (Real.differentiableAt_log one_ne_zero)).tendsto.comp ha
    simpa [Real.deriv_log,Function.comp_def] using h
  have hlog : Tendsto (fun i => (k i : ℝ)*Real.log (a i)) atTop (𝓝 c) := by
    convert hd.mul hds using 1
    · ext i
      have he := sub_smul_dslope Real.log 1 (a i)
      simp only [smul_eq_mul,Real.log_one,sub_zero] at he
      rw [mul_assoc,he]
    · simp
  apply (Real.continuous_exp.tendsto c |>.comp hlog).congr'
  filter_upwards [(tendsto_order.mp ha).1 0 zero_lt_one] with i hi
  dsimp only [Function.comp_def]
  rw [Real.exp_nat_mul,Real.exp_log hi]

lemma gaussian_cosine_power_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ S r) {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) :
    Tendsto (fun i => (∫ x, Real.cos (t*(S x/r i)) ∂μ)^(⌊τ*fluctuationScale μ S (r i)⌋₊))
      atTop (𝓝 (Real.exp (-(τ*t^2/2)))) := by
  have hn : Tendsto (fun i => fluctuationScale μ S (r i)) atTop atTop :=
    (fluctuationScale_tendsto μ S hS hI hne).comp hr.1
  have hd := gaussian_cosine_drift μ S hS hne r hr t
  have hzero : Tendsto (fun i => (∫ x, Real.cos (t*(S x/r i)) ∂μ)-1) atTop (𝓝 0) := by
    have hz := hd.mul (tendsto_inv_atTop_zero.comp hn)
    simp only [mul_zero] at hz
    apply hz.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    dsimp only [Function.comp_def]
    field_simp
  have ha : Tendsto (fun i => ∫ x, Real.cos (t*(S x/r i)) ∂μ) atTop (𝓝 1) := by
    simpa using hzero.add_const 1
  have hk := (tendsto_nat_floor_mul_div_atTop hτ).comp hn
  have hdk : Tendsto (fun i => (⌊τ*fluctuationScale μ S (r i)⌋₊ : ℝ)*
      ((∫ x, Real.cos (t*(S x/r i)) ∂μ)-1)) atTop (𝓝 (-(τ*t^2/2))) := by
    have hc := hk.mul hd
    have he : τ * (-(t^2/2)) = -(τ*t^2/2) := by ring
    rw [he] at hc
    apply hc.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    dsimp only [Function.comp_def]
    field_simp
  exact tendsto_pow_variable_of_drift ha hdk

lemma gaussian_charFun_power_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0})
    (hsym : IdentDistrib S (fun x => -S x) μ μ) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ S r) {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) :
    Tendsto (fun i => (charFun (μ.map S) (t/r i))^(⌊τ*fluctuationScale μ S (r i)⌋₊))
      atTop (𝓝 (Complex.exp (-(τ*t^2/2 : ℝ)))) := by
  convert (gaussian_cosine_power_limit μ S hS hI hne r hr hτ t).ofReal using 1
  · ext i
    rw [symmetric_charFun_cosine μ S hS hsym]
    rw [← Complex.ofReal_pow]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    ring
  · simp

lemma charFun_div_partialSum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hind : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) (r t : ℝ) :
    charFun (μ.map (fun ω => realPartialSum (fun k => X k ω) n / r)) t =
      (charFun (μ.map (X 0)) (t/r)) ^ n := by
  have hm i := (hident i).aemeasurable_fst
  simp only [realPartialSum,div_eq_inv_mul]
  rw [charFun_map_mul_comp, (hind.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ => hm _)]
  · simp [fun i => (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ => hm _

theorem gaussian_iid_marginal_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {x | X 0 x ≠ 0})
    (hsym : IdentDistrib (X 0) (fun x => -X 0 x) μ μ)
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r) (τ : ℝ≥0) :
    TendstoInDistribution
      (fun i ω => realPartialSum (fun k => X k ω)
        (⌊(τ:ℝ)*fluctuationScale μ (X 0) (r i)⌋₊) / r i)
      atTop id (fun _ => μ) (gaussianReal 0 τ) where
  forall_aemeasurable i :=
    (Finset.aemeasurable_fun_sum _ fun k _ => (hX k).aemeasurable).div_const _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    change Tendsto (fun i => charFun (μ.map (fun ω => realPartialSum (fun k => X k ω)
      (⌊(τ:ℝ)*fluctuationScale μ (X 0) (r i)⌋₊) / r i)) t) atTop
      (𝓝 (charFun ((gaussianReal 0 τ).map id) t))
    simp only [Measure.map_id, charFun_div_partialSum μ X hind hident,
      charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
    convert gaussian_charFun_power_limit μ (X 0) (hX 0) hI hne hsym r hr τ.coe_nonneg t using 1
    norm_cast

theorem independent_common_gaussian_marginal {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d)
    (hne : 0 < independentConditionedPairLaw ν ℓ {P | commonIncrementProcess ℓ e 0 P ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν ℓ)
      (commonIncrementProcess ℓ e 0) r) (τ : ℝ≥0) :
    letI : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
      independentConditionedPairLaw_probability ν ℓ
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
    TendstoInDistribution
      (fun i P => realPartialSum (fun k => commonIncrementProcess ℓ e k P)
        (⌊(τ:ℝ)*fluctuationScale (independentConditionedPairLaw ν ℓ)
          (commonIncrementProcess ℓ e 0) (r i)⌋₊) / r i)
      atTop id (fun _ => independentConditionedPairLaw ν ℓ) (gaussianReal 0 τ) := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact gaussian_iid_marginal_limit _ _ (measurable_commonIncrementProcess ℓ e)
    (commonIncrements_independent ν ℓ htrans height hproj hstep e)
    (commonIncrements_identDistrib ν ℓ htrans height hproj hstep e)
    (independent_commonWordIncrement_integrable ν hue ℓ hℓ htrans height hproj hstep e) hne
    (independent_commonWordIncrement_symmetric ν ℓ htrans e) r hr τ

end DirectionalTransience
end
end

end OAI
