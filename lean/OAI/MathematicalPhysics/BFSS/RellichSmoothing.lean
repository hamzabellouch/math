import Mathlib

namespace OAI

/-! Translation estimates and compact smoothing of vector-valued functions. -/

namespace BFSSRellich
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma norm_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → F} (hf : Integrable f μ)
    (hs : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hc : ConvexOn ℝ (univ : Set F) (fun y => ‖y‖ ^ 2) :=
    (convexOn_univ_norm (E := F)).pow (fun _ _ => norm_nonneg _) 2
  exact hc.map_integral_le (by fun_prop) isClosed_univ (by simp) hf hs

abbrev unitInterval : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure unitInterval where
  measure_univ := by simp [unitInterval]

lemma integral_fderiv_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → F} (hf : ContDiff ℝ 1 f) (x y : E) :
    (∫ t, fderiv ℝ f (x + t • y) y ∂unitInterval) = f (x + y) - f x := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • y))
      (fderiv ℝ f (x + t • y) y) t := by
    exact (hf.differentiable (by norm_num) (x + t • y)).hasFDerivAt.comp_hasDerivAt t
      (by simpa only [one_smul, id_eq] using
        ((hasDerivAt_id t).smul_const y |>.const_add x))
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • y) y) :=
    (hf.continuous_fderiv (by norm_num)).comp (by fun_prop) |>.clm_apply continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_of_le zero_le_one, zero_smul, add_zero, one_smul]
    using h

lemma translation_pointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → F} (hf : ContDiff ℝ 1 f) (x y : E) :
    ‖f (x + y) - f x‖ ^ 2 ≤
      ‖y‖ ^ 2 * ∫ t, ‖fderiv ℝ f (x + t • y)‖ ^ 2 ∂unitInterval := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • y)) :=
    (hf.continuous_fderiv (by norm_num)).comp (by fun_prop)
  have hci := (((hc.clm_apply continuous_const).norm.pow 2).integrableOn_Icc :
    IntegrableOn (fun t : ℝ => ‖fderiv ℝ f (x + t • y) y‖ ^ 2) (Icc 0 1))
  have hcf := ((hc.clm_apply continuous_const).integrableOn_Icc :
    IntegrableOn (fun t : ℝ => fderiv ℝ f (x + t • y) y) (Icc 0 1))
  rw [← integral_fderiv_segment hf x y]
  calc
    ‖∫ t, fderiv ℝ f (x + t • y) y ∂unitInterval‖ ^ 2 ≤
        ∫ t, ‖fderiv ℝ f (x + t • y) y‖ ^ 2 ∂unitInterval :=
      norm_integral_sq_le (hcf.mono_set Ioc_subset_Icc_self) (hci.mono_set Ioc_subset_Icc_self)
    _ ≤ ∫ t, ‖y‖ ^ 2 * ‖fderiv ℝ f (x + t • y)‖ ^ 2 ∂unitInterval := by
      apply integral_mono (hci.mono_set Ioc_subset_Icc_self)
        (((hc.norm.pow 2).const_mul (‖y‖ ^ 2)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      intro t
      have h := (fderiv ℝ f (x + t • y)).le_opNorm y
      change ‖fderiv ℝ f (x + t • y) y‖ ^ 2 ≤ ‖y‖ ^ 2 * ‖fderiv ℝ f (x + t • y)‖ ^ 2
      have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
      simpa only [mul_pow, mul_comm] using hh
    _ = _ := integral_const_mul _ _

variable {ι : Type*} [Fintype ι]
abbrev Euclidean := EuclideanSpace ℝ ι

lemma continuous_norm_sq_integrable {G : Type*} [NormedAddCommGroup G]
    {f : Euclidean (ι := ι) → G} (hf : Continuous f) (hfK : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖ ^ (2 : ℕ)) volume := by
  have hc : Continuous (fun x => ‖f x‖ ^ (2 : ℕ)) := hf.norm.pow 2
  have hk : HasCompactSupport (fun x => ‖f x‖ ^ (2 : ℕ)) :=
    hfK.comp_left (g := fun z : G => ‖z‖ ^ (2 : ℕ)) (by simp)
  exact hc.integrable_of_hasCompactSupport hk

omit [CompleteSpace F] in
lemma derivative_norm_sq_integrable {f : Euclidean (ι := ι) → F}
    (hf : ContDiff ℝ 1 f) (hfK : HasCompactSupport f) :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ (2 : ℕ)) volume :=
  continuous_norm_sq_integrable (hf.continuous_fderiv (by norm_num)) (hfK.fderiv ℝ)

lemma translation_integral_bound {f : Euclidean (ι := ι) → F}
    (hf : ContDiff ℝ 1 f) (hfK : HasCompactSupport f) (y : Euclidean (ι := ι)) :
    (∫ x, ‖f (x + y) - f x‖ ^ 2) ≤ ‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  let g : Euclidean (ι := ι) × ℝ → ℝ :=
    fun z => ‖fderiv ℝ f (z.1 + z.2 • y)‖ ^ 2
  have hgc : Continuous g := by
    exact (((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).norm.pow 2)
  have hgi : Integrable g (volume.prod unitInterval) := by
    apply (integrable_prod_iff' hgc.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((measurePreserving_add_right volume (t • y)).integrable_comp
          (derivative_norm_sq_integrable hf hfK).aestronglyMeasurable).mpr
            (derivative_norm_sq_integrable hf hfK)
    · have he : (fun t : ℝ => ∫ x : Euclidean (ι := ι), ‖g (x, t)‖) =
          fun _ => ∫ x : Euclidean (ι := ι), ‖fderiv ℝ f x‖ ^ 2 := by
        funext t
        simp only [g, Real.norm_eq_abs, abs_pow, abs_norm]
        exact integral_add_right_eq_self (μ := volume) (fun x => ‖fderiv ℝ f x‖ ^ 2) (t • y)
      rw [he]
      exact integrable_const _
  have hfi : Integrable (fun x => ‖f (x + y) - f x‖ ^ 2) volume := by
    exact continuous_norm_sq_integrable
      ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)
      ((hfK.comp_homeomorph (Homeomorph.addRight y)).sub hfK)
  have hm := integral_mono hfi (hgi.integral_prod_left.const_mul (‖y‖ ^ 2))
    (fun x => translation_pointwise hf x y)
  calc
    _ ≤ ∫ x, ‖y‖ ^ 2 * ∫ t, g (x, t) ∂unitInterval := hm
    _ = ‖y‖ ^ 2 * ∫ t, ∫ x, g (x, t) ∂volume ∂unitInterval := by
      rw [integral_const_mul, integral_integral_swap hgi]
    _ = _ := by
      have hs (t : ℝ) : (∫ x, g (x, t)) = ∫ x, ‖fderiv ℝ f x‖ ^ 2 :=
        integral_add_right_eq_self (fun x => ‖fderiv ℝ f x‖ ^ 2) (t • y)
      simp only [hs]
      simp

lemma translate_integrable_product {G : Type*} [NormedAddCommGroup G]
    {f : Euclidean (ι := ι) → G} (hf : Continuous f) (hi : Integrable f volume)
    {μ : Measure (Euclidean (ι := ι))} [IsFiniteMeasure μ] :
    Integrable (fun z : Euclidean (ι := ι) × Euclidean (ι := ι) => f (z.1 + z.2))
      (volume.prod μ) := by
  apply (integrable_prod_iff' (hf.comp (by fun_prop)).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun y =>
      ((measurePreserving_add_right volume y).integrable_comp hi.aestronglyMeasurable).mpr hi
  · have he : (fun y : Euclidean (ι := ι) => ∫ x : Euclidean (ι := ι), ‖f (x + y)‖) =
        fun _ => ∫ x : Euclidean (ι := ι), ‖f x‖ := by
      funext y
      exact integral_add_right_eq_self (fun x => ‖f x‖) y
    change Integrable (fun y : Euclidean (ι := ι) => ∫ x : Euclidean (ι := ι), ‖f (x + y)‖) μ
    rw [he]
    exact integrable_const _

lemma first_integrable_product {G : Type*} [NormedAddCommGroup G]
    {f : Euclidean (ι := ι) → G} (hf : Continuous f) (hi : Integrable f volume)
    {μ : Measure (Euclidean (ι := ι))} [IsFiniteMeasure μ] :
    Integrable (fun z : Euclidean (ι := ι) × Euclidean (ι := ι) => f z.1)
      (volume.prod μ) := by
  apply (integrable_prod_iff' (hf.comp continuous_fst).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall fun _ => hi, ?_⟩
  exact (integrable_const (∫ x : Euclidean (ι := ι), ‖f x‖) :
    Integrable (fun _ : Euclidean (ι := ι) => ∫ x : Euclidean (ι := ι), ‖f x‖) μ)

omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma norm_sub_sq_le (a b : F) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma translate_sub_square_integrable_product {f : Euclidean (ι := ι) → F}
    (hf : Continuous f) (hfK : HasCompactSupport f)
    {μ : Measure (Euclidean (ι := ι))} [IsFiniteMeasure μ] :
    Integrable (fun z : Euclidean (ι := ι) × Euclidean (ι := ι) => ‖f (z.1 + z.2) - f z.1‖ ^ 2)
      (volume.prod μ) := by
  have hi := continuous_norm_sq_integrable hf hfK
  have hs := ((translate_integrable_product (hf.norm.pow 2) hi (μ := μ)).const_mul 2).add
    ((first_integrable_product (hf.norm.pow 2) hi (μ := μ)).const_mul 2)
  apply hs.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sub_sq_le _ _

def smoothAverage (μ : Measure (Euclidean (ι := ι))) (f : Euclidean (ι := ι) → F)
    (x : Euclidean (ι := ι)) : F := ∫ y, f (x + y) ∂μ

lemma smoothAverage_sub_eq {f : Euclidean (ι := ι) → F}
    (hf : Continuous f) (hfK : HasCompactSupport f)
    {μ : Measure (Euclidean (ι := ι))} [IsProbabilityMeasure μ] (x : Euclidean (ι := ι)) :
    smoothAverage μ f x - f x = ∫ y, f (x + y) - f x ∂μ := by
  have hi : Integrable (fun y => f (x + y)) μ :=
    (hf.comp (continuous_const.add continuous_id)).integrable_of_hasCompactSupport
      (hfK.comp_homeomorph (Homeomorph.addLeft x))
  rw [integral_sub hi (integrable_const _)]
  simp [smoothAverage]

lemma smoothAverage_Jensen {f : Euclidean (ι := ι) → F}
    (hf : Continuous f) (hfK : HasCompactSupport f)
    {μ : Measure (Euclidean (ι := ι))} [IsProbabilityMeasure μ] (x : Euclidean (ι := ι)) :
    ‖smoothAverage μ f x - f x‖ ^ 2 ≤ ∫ y, ‖f (x + y) - f x‖ ^ 2 ∂μ := by
  have hc : Continuous (fun y => f (x + y) - f x) :=
    (hf.comp (continuous_const.add continuous_id)).sub continuous_const
  obtain ⟨C, hC⟩ := (hfK.isCompact_range hf).isBounded.exists_norm_le
  have hb (y : Euclidean (ι := ι)) : ‖f (x + y) - f x‖ ≤ C + C :=
    (norm_sub_le _ _).trans (add_le_add (hC _ ⟨x + y, rfl⟩) (hC _ ⟨x, rfl⟩))
  have hi : Integrable (fun y => f (x + y) - f x) μ :=
    (integrable_const (C + C)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  have hs : Integrable (fun y => ‖f (x + y) - f x‖ ^ 2) μ := by
    apply (integrable_const ((C + C) ^ 2)).mono' (hc.norm.pow 2).aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb y) 2
  rw [smoothAverage_sub_eq hf hfK x]
  exact norm_integral_sq_le hi hs

lemma smoothAverage_sub_square_integrable {f : Euclidean (ι := ι) → F}
    (hf : Continuous f) (hfK : HasCompactSupport f)
    {μ : Measure (Euclidean (ι := ι))} [IsProbabilityMeasure μ] :
    Integrable (fun x => ‖smoothAverage μ f x - f x‖ ^ 2) volume := by
  have hi := translate_sub_square_integrable_product hf hfK (μ := μ)
  have ht := translate_integrable_product hf
    (hf.integrable_of_hasCompactSupport hfK) (μ := μ)
  have hm : AEStronglyMeasurable (fun x => ‖smoothAverage μ f x - f x‖ ^ 2) volume :=
    (ht.integral_prod_left.aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2
  apply hi.integral_prod_left.mono' hm
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact smoothAverage_Jensen hf hfK x

theorem smoothAverage_error {f : Euclidean (ι := ι) → F}
    (hf : ContDiff ℝ 1 f) (hfK : HasCompactSupport f)
    {μ : Measure (Euclidean (ι := ι))} [IsProbabilityMeasure μ] {r : ℝ}
    (_hr : 0 ≤ r) (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ r) :
    (∫ x, ‖smoothAverage μ f x - f x‖ ^ 2) ≤ r ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hi := translate_sub_square_integrable_product hf.continuous hfK (μ := μ)
  have ht := translate_integrable_product hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hfK) (μ := μ)
  have hm : AEStronglyMeasurable (fun x => ‖smoothAverage μ f x - f x‖ ^ 2) volume :=
    (ht.integral_prod_left.aestronglyMeasurable.sub hf.continuous.aestronglyMeasurable).norm.pow 2
  have hs : Integrable (fun x => ‖smoothAverage μ f x - f x‖ ^ 2) volume := by
    apply hi.integral_prod_left.mono' hm
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact smoothAverage_Jensen hf.continuous hfK x
  have hb : (∫ x, ‖smoothAverage μ f x - f x‖ ^ 2) ≤
      ∫ y, ∫ x, ‖f (x + y) - f x‖ ^ 2 ∂volume ∂μ := by
    rw [← integral_integral_swap hi]
    exact integral_mono hs hi.integral_prod_left (smoothAverage_Jensen hf.continuous hfK)
  apply hb.trans
  have hgrad : 0 ≤ ∫ x, ‖fderiv ℝ f x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ ∫ _y, r ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂volume ∂μ := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      filter_upwards [hμ] with y hy
      exact (translation_integral_bound hf hfK y).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hy 2) hgrad)
    _ = _ := by simp

def kernelAverage (κ : Euclidean (ι := ι) → ℝ) (f : Euclidean (ι := ι) → F)
    (x : Euclidean (ι := ι)) : F := ∫ y, κ (y - x) • f y

omit [CompleteSpace F] in
lemma kernel_integrable {κ : Euclidean (ι := ι) → ℝ}
    (hκ : Continuous κ) {C : ℝ} (hC : ∀ x, ‖κ x‖ ≤ C)
    {f : Euclidean (ι := ι) → F} (hf : Integrable f volume) (x : Euclidean (ι := ι)) :
    Integrable (fun y => κ (y - x) • f y) volume := by
  apply (hf.norm.const_mul C).mono'
    (((hκ.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).smul hf.aestronglyMeasurable)
  filter_upwards with y
  change ‖κ (y - x) • f y‖ ≤ C * ‖f y‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC (y - x)) (norm_nonneg _)

omit [CompleteSpace F] in
lemma kernelAverage_bound {κ : Euclidean (ι := ι) → ℝ}
    (hκ : Continuous κ) {C : ℝ} (hC : ∀ x, ‖κ x‖ ≤ C)
    {f : Euclidean (ι := ι) → F} (hf : Integrable f volume) (x : Euclidean (ι := ι)) :
    ‖kernelAverage κ f x‖ ≤ C * ∫ y, ‖f y‖ := by
  calc
    _ ≤ ∫ y, ‖κ (y - x) • f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * ‖f y‖ := by
      apply integral_mono (kernel_integrable hκ hC hf x).norm (hf.norm.const_mul C)
      intro y
      change ‖κ (y - x) • f y‖ ≤ C * ‖f y‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC (y - x)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

omit [CompleteSpace F] in
lemma kernelAverage_lipschitz {κ : Euclidean (ι := ι) → ℝ}
    {L : ℝ≥0} (hκ : LipschitzWith L κ) {C : ℝ} (hC : ∀ x, ‖κ x‖ ≤ C)
    {f : Euclidean (ι := ι) → F} (hf : Integrable f volume) {B : ℝ≥0}
    (hB : (∫ y, ‖f y‖) ≤ B) :
    LipschitzWith (L * B) (kernelAverage κ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [dist_eq_norm]
  have he : kernelAverage κ f x - kernelAverage κ f z =
      ∫ y, (κ (y - x) - κ (y - z)) • f y := by
    simp only [kernelAverage, sub_smul]
    rw [integral_sub (kernel_integrable hκ.continuous hC hf x)
      (kernel_integrable hκ.continuous hC hf z)]
  rw [he]
  calc
    _ ≤ ∫ y, ‖(κ (y - x) - κ (y - z)) • f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (L : ℝ) * dist x z * ‖f y‖ := by
      have hi := ((kernel_integrable hκ.continuous hC hf x).sub
          (kernel_integrable hκ.continuous hC hf z)).norm
      change Integrable (fun y => ‖κ (y - x) • f y - κ (y - z) • f y‖) volume at hi
      simp only [← sub_smul] at hi
      apply integral_mono hi (hf.norm.const_mul ((L : ℝ) * dist x z))
      intro y
      change ‖(κ (y - x) - κ (y - z)) • f y‖ ≤ (L : ℝ) * dist x z * ‖f y‖
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hd : dist (y - x) (y - z) = dist x z := by
        rw [dist_eq_norm, dist_eq_norm,
          show y - x - (y - z) = -(x - z) by abel, norm_neg]
      calc
        _ = dist (κ (y - x)) (κ (y - z)) := (dist_eq_norm _ _).symm
        _ ≤ (L : ℝ) * dist (y - x) (y - z) := hκ.dist_le_mul _ _
        _ = _ := by rw [hd]
    _ = (L : ℝ) * dist x z * ∫ y, ‖f y‖ := integral_const_mul _ _
    _ ≤ (L : ℝ) * dist x z * B :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg L.coe_nonneg dist_nonneg)
    _ = _ := by simp only [NNReal.coe_mul]; ring

variable (φ : ContDiffBump (0 : Euclidean (ι := ι)))

def bumpMeasure : Measure (Euclidean (ι := ι)) :=
  volume.withDensity (fun y => ENNReal.ofReal (φ.normed volume y))

instance bumpMeasure_probability : IsProbabilityMeasure (bumpMeasure φ) where
  measure_univ := by
    rw [bumpMeasure, withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed]
    · rw [φ.integral_normed, ENNReal.ofReal_one]
    · exact Filter.Eventually.of_forall φ.nonneg_normed

lemma bumpMeasure_supported : ∀ᵐ y ∂bumpMeasure φ, ‖y‖ ≤ φ.rOut := by
  rw [bumpMeasure, ae_withDensity_iff (φ.continuous_normed.measurable.ennreal_ofReal)]
  filter_upwards with y hy
  have hκ : φ.normed volume y ≠ 0 := by
    intro hz
    simp [hz] at hy
  have h := (φ.support_normed_eq (μ := volume)).subset hκ
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using h)

omit [CompleteSpace F] in
lemma kernelAverage_eq_smoothAverage (f : Euclidean (ι := ι) → F) (x : Euclidean (ι := ι)) :
    kernelAverage (φ.normed volume) f x = smoothAverage (bumpMeasure φ) f x := by
  rw [smoothAverage, bumpMeasure,
    integral_withDensity_eq_integral_toReal_smul (φ.continuous_normed.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _)]
  have he := integral_add_left_eq_self (μ := volume)
    (fun y => φ.normed volume (y - x) • f y) x
  simpa only [kernelAverage, add_sub_cancel_left] using he.symm

theorem kernelAverage_error {f : Euclidean (ι := ι) → F}
    (hf : ContDiff ℝ 1 f) (hfK : HasCompactSupport f) :
    (∫ x, ‖kernelAverage (φ.normed volume) f x - f x‖ ^ 2) ≤
      φ.rOut ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  simp only [kernelAverage_eq_smoothAverage]
  exact smoothAverage_error hf hfK φ.rOut_pos.le (bumpMeasure_supported φ)

end
end BFSSRellich

end OAI
