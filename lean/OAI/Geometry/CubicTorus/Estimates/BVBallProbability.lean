import Mathlib
import OAI.Geometry.CubicTorus.Estimates.UnitAngle

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma lipschitz_affine_line {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a h : X) : LipschitzWith ‖h‖₊ (fun t : ℝ ↦ a + t • h) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs,
    Real.dist_eq]
  exact le_of_eq (mul_comm _ _)

theorem lipschitz_translation_square_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    (h : X) :
    Integrable (fun x ↦ (f (x + h) - f x) ^ 2) μ ∧
      (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤
        ‖h‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  let G : X × ℝ → ℝ := fun p ↦ ‖fderiv ℝ f (p.1 + p.2 • h)‖ ^ 2
  have hν : ν.real univ = 1 := by norm_num [ν, measureReal_def, Real.volume_Icc]
  have hflow : Continuous (fun p : X × ℝ ↦ p.1 + p.2 • h) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hG : Measurable G := ((measurable_fderiv ℝ f).comp hflow.measurable).norm.pow_const 2
  have hmd : MeasurableSet {p : X × ℝ | DifferentiableAt ℝ f (p.1 + p.2 • h)} :=
    (measurableSet_of_differentiableAt ℝ f).preimage hflow.measurable
  have hdiff : ∀ᵐ x ∂μ, ∀ᵐ t ∂ν, DifferentiableAt ℝ f (x + t • h) := by
    apply (Measure.ae_ae_comm hmd).mpr
    exact ae_of_all _ fun t ↦ (measurePreserving_add_right μ (t • h)).quasiMeasurePreserving.ae
      hf.ae_differentiableAt
  have htI (t : ℝ) : Integrable (fun x ↦ G (x, t)) μ :=
    (measurePreserving_add_right μ (t • h)).integrable_comp hgrad.aestronglyMeasurable |>.mpr hgrad
  have hswap : Integrable (fun p : ℝ × X ↦ G (p.2, p.1)) (ν.prod μ) := by
    apply (integrable_prod_iff (hG.comp measurable_swap).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ htI, ?_⟩
    have he : (fun t ↦ ∫ x, ‖G (x, t)‖ ∂μ) =
        (fun _ : ℝ ↦ ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) := by
      funext t
      dsimp only [G]
      simp only [Real.norm_eq_abs, abs_pow, abs_norm]
      exact integral_add_right_eq_self (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) (t • h)
    change Integrable (fun t ↦ ∫ x, ‖G (x, t)‖ ∂μ) ν
    rw [he]
    exact integrable_const _
  have hprod : Integrable G (μ.prod ν) := hswap.swap
  have hGI : Integrable (fun x ↦ ∫ t, G (x, t) ∂ν) μ := hprod.integral_prod_left
  have hpoint : ∀ᵐ x ∂μ, (f (x + h) - f x) ^ 2 ≤
      ‖h‖ ^ 2 * ∫ t, G (x, t) ∂ν := by
    filter_upwards [hdiff, hprod.prod_right_ae] with x hx hi
    have hl : LipschitzWith (K * ‖h‖₊) (fun t : ℝ ↦ f (x + t • h)) :=
      hf.comp (lipschitz_affine_line x h)
    have hFTC := lipschitz_sq_sub_le_interval_energy hl (by norm_num : (0 : ℝ) ≤ 1)
    simp only [one_smul, zero_smul, add_zero, sub_zero, one_mul] at hFTC
    apply hFTC.trans
    have hc : ∀ᵐ t ∂ν, deriv (fun s : ℝ ↦ f (x + s • h)) t ^ 2 ≤
        ‖h‖ ^ 2 * G (x, t) := by
      filter_upwards [hx] with t ht
      have he : deriv (fun s : ℝ ↦ f (x + s • h)) t = fderiv ℝ f (x + t • h) h := by
        have hh := ht.hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).smul_const h |>.const_add x)
        simpa only [Function.comp_def, one_smul, id_eq] using hh.deriv
      rw [he]
      have hb := (fderiv ℝ f (x + t • h)).le_opNorm h
      rw [Real.norm_eq_abs] at hb
      dsimp [G]
      nlinarith [sq_abs (fderiv ℝ f (x + t • h) h),
        abs_nonneg (fderiv ℝ f (x + t • h) h),
        mul_nonneg (norm_nonneg (fderiv ℝ f (x + t • h))) (norm_nonneg h)]
    have hh := integral_mono_ae (lipschitz_deriv_sq_integrableOn hl 0 1)
      (hi.const_mul (‖h‖ ^ 2)) hc
    simpa only [integral_const_mul] using hh
  have hleft : Integrable (fun x ↦ (f (x + h) - f x) ^ 2) μ := by
    apply (hGI.const_mul (‖h‖ ^ 2)).mono'
      (((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous).pow 2).aestronglyMeasurable
    filter_upwards [hpoint] with x hx
    change ‖(f (x + h) - f x) ^ 2‖ ≤ _
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hleft, (integral_mono_ae hleft (hGI.const_mul (‖h‖ ^ 2)) hpoint).trans_eq ?_⟩
  rw [integral_const_mul, integral_integral_swap hprod]
  have he : (∫ t, ∫ x, G (x, t) ∂μ ∂ν) = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    have htint (t : ℝ) : (∫ x, G (x, t) ∂μ) = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
      integral_add_right_eq_self (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) (t • h)
    simp only [htint, integral_const, smul_eq_mul, hν, one_mul]
  rw [he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem lipschitz_average_translation_square_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {ν : Measure X} [IsProbabilityMeasure ν]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hν : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) :
    Integrable (fun x ↦ (∫ y, f (x - y) - f x ∂ν) ^ 2) μ ∧
      (∫ x, (∫ y, f (x - y) - f x ∂ν) ^ 2 ∂μ) ≤
        δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  let D : X × X → ℝ := fun p ↦ f (p.2 - p.1) - f p.2
  have hD : Continuous D :=
    (hf.continuous.comp (continuous_snd.sub continuous_fst)).sub
      (hf.continuous.comp continuous_snd)
  have hdpoint (x : X) : ∀ᵐ y ∂ν, |D (y, x)| ≤ (K : ℝ) * δ := by
    filter_upwards [hν] with y hy
    have hh := hf.dist_le_mul (x - y) x
    rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
  have hdi (x : X) : Integrable (fun y ↦ D (y, x)) ν := by
    apply (integrable_const ((K : ℝ) * δ)).mono'
      (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, Function.comp_def, id_eq] using hdpoint x
  have hdi₂ (x : X) : Integrable (fun y ↦ D (y, x) ^ 2) ν := by
    apply (integrable_const (((K : ℝ) * δ) ^ 2)).mono'
      ((hD.comp (continuous_id.prodMk continuous_const)).pow 2).aestronglyMeasurable
    filter_upwards [hdpoint x] with y hy
    change ‖D (y, x) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (D (y, x)), abs_nonneg (D (y, x)), mul_nonneg K.coe_nonneg hδ]
  have hJ (y : X) : Integrable (fun x ↦ D (y, x) ^ 2) μ ∧
      (∫ x, D (y, x) ^ 2 ∂μ) ≤ ‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    simpa only [D, sub_eq_add_neg, norm_neg] using lipschitz_translation_square_le hf hgrad (-y)
  have hJe : ∀ᵐ y ∂ν, (∫ x, D (y, x) ^ 2 ∂μ) ≤
      δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    filter_upwards [hν] with y hy
    apply (hJ y).2.trans
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ ↦ sq_nonneg _))
    nlinarith [norm_nonneg y]
  have hprod : Integrable (fun p : X × X ↦ D p ^ 2) (ν.prod μ) := by
    apply (integrable_prod_iff (hD.pow 2).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ fun y ↦ (hJ y).1, ?_⟩
    have he (y : X) : (∫ x, ‖D (y, x) ^ 2‖ ∂μ) = ∫ x, D (y, x) ^ 2 ∂μ := by
      congr 1
      funext x
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun y ↦ ∫ x, ‖D (y, x) ^ 2‖ ∂μ) ν
    simp_rw [he]
    apply (integrable_const (δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ)).mono'
      (hD.pow 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hJe] with y hy
    rwa [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))]
  have hA (x : X) : (∫ y, D (y, x) ∂ν) ^ 2 ≤ ∫ y, D (y, x) ^ 2 ∂ν := by
    have hh := integral_square_le_mass (hdi x) (hdi₂ x)
    simpa only [probReal_univ, one_mul] using hh
  have hAI : Integrable (fun x ↦ (∫ y, D (y, x) ∂ν) ^ 2) μ := by
    apply hprod.integral_prod_right.mono'
      (hD.stronglyMeasurable.integral_prod_left'.pow 2).aestronglyMeasurable
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hA x
  refine ⟨hAI, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, D (y, x) ^ 2 ∂ν ∂μ :=
      integral_mono hAI hprod.integral_prod_right hA
    _ = ∫ y, ∫ x, D (y, x) ^ 2 ∂μ ∂ν := integral_integral_swap hprod.swap
    _ ≤ ∫ _y, δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ ∂ν :=
      integral_mono_ae hprod.integral_prod_left (integrable_const _) hJe
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma probability_dominated_square {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsProbabilityMeasure ν] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hν : ν ≤ c • μ) {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfs : Integrable (fun x ↦ f x ^ 2) μ) :
    Integrable f ν ∧ Integrable (fun x ↦ f x ^ 2) ν ∧
      (∫ x, f x ∂ν) ^ 2 ≤ c.toReal * ∫ x, f x ^ 2 ∂μ := by
  have hi : Integrable (fun x ↦ f x ^ 2) ν := (hfs.smul_measure hc).mono_measure hν
  have hm : AEStronglyMeasurable f ν := (hf.smul_measure c).mono_measure hν
  have him : MemLp f 2 ν := (memLp_two_iff_integrable_sq hm).mpr hi
  have hif : Integrable f ν := him.integrable (by norm_num)
  refine ⟨hif, hi, ?_⟩
  have hj := integral_square_le_mass hif hi
  simp only [probReal_univ, one_mul] at hj
  apply hj.trans
  have hb := integral_mono_measure hν (ae_of_all _ fun x ↦ sq_nonneg (f x))
    (hfs.smul_measure hc)
  simpa only [integral_smul_measure, smul_eq_mul] using hb

theorem h1_average_bounds {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {ν : Measure X} [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hν : ν ≤ c • μ)
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfs : Integrable (fun x ↦ f x ^ 2) μ)
    (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    {M D : ℝ} (hM : (∫ x, f x ^ 2 ∂μ) ≤ M)
    (hD : (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) ≤ D) :
    (∀ x, |∫ y, f (x - y) ∂ν| ≤ Real.sqrt (c.toReal * M)) ∧
      LipschitzWith ⟨Real.sqrt (c.toReal * D), Real.sqrt_nonneg _⟩
        (fun x ↦ ∫ y, f (x - y) ∂ν) := by
  have ht (x : X) : Integrable (fun y ↦ f (x - y) ^ 2) μ :=
    (μ.measurePreserving_sub_left x).integrable_comp hfs.aestronglyMeasurable |>.mpr hfs
  have hp (x : X) := probability_dominated_square (f := fun y ↦ f (x - y)) hc hν
    ((hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) (ht x)
  have hMnon : 0 ≤ M := (integral_nonneg (fun _ ↦ sq_nonneg _)).trans hM
  have hDnon : 0 ≤ D := (integral_nonneg (fun _ ↦ sq_nonneg _)).trans hD
  constructor
  · intro x
    apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg ENNReal.toReal_nonneg hMnon)).mpr
    rw [sq_abs]
    apply (hp x).2.2.trans
    rw [integral_sub_left_eq_self (fun y ↦ f y ^ 2) μ x]
    exact mul_le_mul_of_nonneg_left hM ENNReal.toReal_nonneg
  · apply LipschitzWith.of_dist_le_mul
    intro x z
    have hj := lipschitz_translation_square_le hf hgrad (x - z)
    have hi : Integrable (fun y ↦ (f (x - y) - f (z - y)) ^ 2) μ := by
      have hh := (μ.measurePreserving_sub_left z).integrable_comp hj.1.aestronglyMeasurable |>.mpr hj.1
      have heq (y : X) : z - y + (x - z) = x - y := by abel
      simpa only [Function.comp_def, heq] using hh
    have hp' := probability_dominated_square (f := fun y ↦ f (x - y) - f (z - y)) hc hν
      (((hf.continuous.comp (continuous_const.sub continuous_id)).sub
        (hf.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable) hi
    have he : (∫ y, (f (x - y) - f (z - y)) ^ 2 ∂μ) =
        ∫ y, (f (y + (x - z)) - f y) ^ 2 ∂μ := by
      have hh := integral_sub_left_eq_self (fun y ↦ (f (y + (x - z)) - f y) ^ 2) μ z
      have heq (y : X) : z - y + (x - z) = x - y := by abel
      simpa only [heq] using hh
    rw [integral_sub (hp x).1 (hp z).1, he] at hp'
    have hb := hp'.2.2.trans (mul_le_mul_of_nonneg_left hj.2 ENNReal.toReal_nonneg)
    have hs := mul_le_mul_of_nonneg_left hD (mul_nonneg (show 0 ≤ c.toReal from ENNReal.toReal_nonneg) (sq_nonneg ‖x - z‖))
    rw [Real.dist_eq, dist_eq_norm]
    change |(∫ y, f (x - y) ∂ν) - ∫ y, f (z - y) ∂ν| ≤
      Real.sqrt (c.toReal * D) * ‖x - z‖
    have hr := Real.sq_sqrt (mul_nonneg (show 0 ≤ c.toReal from ENNReal.toReal_nonneg) hDnon)
    nlinarith [sq_abs ((∫ y, f (x - y) ∂ν) - ∫ y, f (z - y) ∂ν),
      abs_nonneg ((∫ y, f (x - y) ∂ν) - ∫ y, f (z - y) ∂ν),
      mul_nonneg (Real.sqrt_nonneg (c.toReal * D)) (norm_nonneg (x - z))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [μ.IsAddHaarMeasure]

def ballProbability (δ : ℝ) : Measure X :=
  (μ (closedBall 0 δ))⁻¹ • μ.restrict (closedBall 0 δ)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] in
lemma closedBall_haar_ne_zero {δ : ℝ} (hδ : 0 < δ) : μ (closedBall (0 : X) δ) ≠ 0 := by
  apply ne_of_gt
  exact (isOpen_ball.measure_pos μ (nonempty_ball.mpr hδ)).trans_le
    (measure_mono ball_subset_closedBall)

omit [BorelSpace X] in
lemma ballProbability_isProbability {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (ballProbability μ δ) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [ballProbability, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (closedBall_haar_ne_zero μ hδ)
    (isCompact_closedBall (0 : X) δ).measure_lt_top.ne

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] [μ.IsAddHaarMeasure] in
lemma ballProbability_domination (δ : ℝ) :
    ballProbability μ δ ≤ (μ (closedBall (0 : X) δ))⁻¹ • μ := by
  dsimp only [ballProbability]
  gcongr
  exact Measure.restrict_le_self

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [μ.IsAddHaarMeasure] in
lemma ballProbability_ae_norm_le (δ : ℝ) :
    ∀ᵐ y ∂ballProbability μ δ, ‖y‖ ≤ δ := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
  simpa only [mem_closedBall, dist_zero_right] using hy

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] in
lemma ballProbability_density_ne_top {δ : ℝ} (hδ : 0 < δ) :
    (μ (closedBall (0 : X) δ))⁻¹ ≠ ⊤ := by
  exact ENNReal.inv_ne_top.mpr (closedBall_haar_ne_zero μ hδ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma boundedContinuous_L2_dist_sq {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {η : Measure Y} [IsFiniteMeasure η]
    (f g : BoundedContinuousFunction Y ℝ) :
    dist ((BoundedContinuousFunction.toLp 2 η ℝ) f)
      ((BoundedContinuousFunction.toLp 2 η ℝ) g) ^ 2 = ∫ y, (f y - g y) ^ 2 ∂η := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub ((BoundedContinuousFunction.toLp 2 η ℝ) f)
    ((BoundedContinuousFunction.toLp 2 η ℝ) g),
    BoundedContinuousFunction.coeFn_toLp 2 η ℝ f,
    BoundedContinuousFunction.coeFn_toLp 2 η ℝ g] with y hy hf hg
  rw [hy]
  change (((BoundedContinuousFunction.toLp 2 η ℝ) f) y -
    ((BoundedContinuousFunction.toLp 2 η ℝ) g) y) *
    (((BoundedContinuousFunction.toLp 2 η ℝ) f) y -
    ((BoundedContinuousFunction.toLp 2 η ℝ) g) y) = _
  rw [hf, hg, pow_two]

lemma h1_average_error {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {ν : Measure X} [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hν : ν ≤ c • μ)
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfs : Integrable (fun x ↦ f x ^ 2) μ)
    (hgrad : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδν : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) :
    Integrable (fun x ↦ ((∫ y, f (x - y) ∂ν) - f x) ^ 2) μ ∧
      (∫ x, ((∫ y, f (x - y) ∂ν) - f x) ^ 2 ∂μ) ≤
        δ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  have hi (x : X) : Integrable (fun y ↦ f (x - y)) ν := by
    have ht : Integrable (fun y ↦ f (x - y) ^ 2) μ :=
      (μ.measurePreserving_sub_left x).integrable_comp hfs.aestronglyMeasurable |>.mpr hfs
    exact (probability_dominated_square (f := fun y ↦ f (x - y)) hc hν
      (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ht).1
  have he (x : X) : (∫ y, f (x - y) - f x ∂ν) = (∫ y, f (x - y) ∂ν) - f x := by
    rw [integral_sub (hi x) (integrable_const _), integral_const, probReal_univ, one_smul]
  simpa only [he] using lipschitz_average_translation_square_le hf hgrad hδ hδν

theorem totallyBounded_local_H1 {X Y ι : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {η : Measure Y} [IsFiniteMeasure η] {e : Y → X} (he : LipschitzWith 1 e)
    (hmap : Measure.map e η ≤ μ) (f : ι → X → ℝ) (K : ι → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (hfs : ∀ i, Integrable (fun x ↦ f i x ^ 2) μ)
    (hgrad : ∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖ ^ 2) μ)
    {M D : ℝ} (hDnon : 0 ≤ D)
    (hM : ∀ i, (∫ x, f i x ^ 2 ∂μ) ≤ M)
    (hD : ∀ i, (∫ x, ‖fderiv ℝ (f i) x‖ ^ 2 ∂μ) ≤ D) :
    TotallyBounded (range (fun i ↦ (BoundedContinuousFunction.toLp 2 η ℝ)
      (BoundedContinuousFunction.mkOfCompact
        ⟨fun y ↦ f i (e y), (hf i).continuous.comp he.continuous⟩))) := by
  let F : ι → BoundedContinuousFunction Y ℝ := fun i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun y ↦ f i (e y), (hf i).continuous.comp he.continuous⟩
  let T : (BoundedContinuousFunction Y ℝ) →L[ℝ] Lp ℝ 2 η :=
    BoundedContinuousFunction.toLp 2 η ℝ
  change TotallyBounded (range (fun i ↦ T (F i)))
  rw [Metric.totallyBounded_iff]
  intro ε hε
  let δ := ε / (2 * (Real.sqrt D + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  let ν := ballProbability μ δ
  let c := (μ (Metric.closedBall (0 : X) δ))⁻¹
  let : IsProbabilityMeasure ν := ballProbability_isProbability μ hδ
  have hc : c ≠ ⊤ := ballProbability_density_ne_top μ hδ
  have hν : ν ≤ c • μ := ballProbability_domination μ δ
  let L : ℝ≥0 := ⟨Real.sqrt (c.toReal * D), Real.sqrt_nonneg _⟩
  have hb (i) := h1_average_bounds hc hν (hf i) (hfs i) (hgrad i) (hM i) (hD i)
  let G : ι → BoundedContinuousFunction Y ℝ := fun i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ ∫ y, f i (e x - y) ∂ν, (hb i).2.continuous.comp he.continuous⟩
  have hl (i) : LipschitzWith L (G i) := by
    change LipschitzWith L ((fun x ↦ ∫ y, f i (x - y) ∂ν) ∘ e)
    convert (hb i).2.comp he using 1
    exact (mul_one L).symm
  have hEq : Equicontinuous ((↑) : range G → Y → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    rintro ⟨_, i, rfl⟩
    exact hl i
  have hbounded (g : BoundedContinuousFunction Y ℝ) (x : Y) (hg : g ∈ range G) :
      g x ∈ Icc (-Real.sqrt (c.toReal * M)) (Real.sqrt (c.toReal * M)) := by
    obtain ⟨i, rfl⟩ := hg
    exact abs_le.mp ((hb i).1 (e x))
  have hcompact := BoundedContinuousFunction.arzela_ascoli
    (Icc (-Real.sqrt (c.toReal * M)) (Real.sqrt (c.toReal * M))) isCompact_Icc
    (range G) hbounded hEq
  have htb : TotallyBounded (range (fun i ↦ T (G i))) := by
    apply (hcompact.image T.continuous).totallyBounded.subset
    rintro _ ⟨i, rfl⟩
    exact ⟨G i, subset_closure (mem_range_self i), rfl⟩
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (half_pos hε)
  refine ⟨s, hs, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨z, hz, hiz⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨z, hz, ?_⟩
  have herr := h1_average_error hc hν (hf i) (hfs i) (hgrad i) hδ.le
    (ballProbability_ae_norm_le μ δ)
  have hlocal : (∫ y, ((∫ z, f i (e y - z) ∂ν) - f i (e y)) ^ 2 ∂η) ≤
      δ ^ 2 * D := by
    have hi := herr.1.mono_measure hmap
    rw [← integral_map he.continuous.measurable.aemeasurable hi.aestronglyMeasurable]
    exact (integral_mono_measure hmap (ae_of_all _ fun _ ↦ sq_nonneg _) herr.1).trans
      (herr.2.trans (mul_le_mul_of_nonneg_left (hD i) (sq_nonneg δ)))
  have hdist : dist (T (F i)) (T (G i)) ≤ δ * Real.sqrt D := by
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg hδ.le (Real.sqrt_nonneg _))).mp
    rw [boundedContinuous_L2_dist_sq, mul_pow, Real.sq_sqrt hDnon]
    calc
      (∫ y, ((F i) y - (G i) y) ^ 2 ∂η) =
          (∫ y, ((∫ z, f i (e y - z) ∂ν) - f i (e y)) ^ 2 ∂η) := by
        apply integral_congr_ae
        filter_upwards [] with y
        change (f i (e y) - (∫ z, f i (e y - z) ∂ν)) ^ 2 =
          ((∫ z, f i (e y - z) ∂ν) - f i (e y)) ^ 2
        ring
      _ ≤ δ ^ 2 * D := hlocal
  have hsmall : δ * Real.sqrt D < ε / 2 := by
    have hden : 0 < 2 * (Real.sqrt D + 1) := by positivity
    have heq : δ * (2 * (Real.sqrt D + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  have hiz' : dist (T (G i)) z < ε / 2 := hiz
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem local_H1_subsequence {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {η : Measure Y} [IsFiniteMeasure η] {e : Y → X} (he : LipschitzWith 1 e)
    (hmap : Measure.map e η ≤ μ) (f : ℕ → X → ℝ) (K : ℕ → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i))
    (hfs : ∀ i, Integrable (fun x ↦ f i x ^ 2) μ)
    (hgrad : ∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖ ^ 2) μ)
    {M D : ℝ} (hDnon : 0 ≤ D)
    (hM : ∀ i, (∫ x, f i x ^ 2 ∂μ) ≤ M)
    (hD : ∀ i, (∫ x, ‖fderiv ℝ (f i) x‖ ^ 2 ∂μ) ≤ D) :
    ∃ g : Lp ℝ 2 η, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ (BoundedContinuousFunction.toLp 2 η ℝ)
        (BoundedContinuousFunction.mkOfCompact
          ⟨fun y ↦ f (φ i) (e y), (hf (φ i)).continuous.comp he.continuous⟩))
        atTop (𝓝 g) := by
  have ht := totallyBounded_local_H1 he hmap f K hf hfs hgrad hDnon hM hD
  obtain ⟨g, _, φ, hφ, hg⟩ := (ht.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    (fun i ↦ subset_closure (mem_range_self i))
  exact ⟨g, φ, hφ, hg⟩

lemma L2_pairing_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ} (hg : Tendsto g atTop (𝓝 u))
    (v : Lp ℝ 2 μ) :
    Tendsto (fun i ↦ ∫ x, g i x * v x ∂μ) atTop (𝓝 (∫ x, u x * v x ∂μ)) := by
  have hh := hg.inner tendsto_const_nhds (𝕜 := ℝ) (g := fun _ : ℕ ↦ v)
  simpa only [L2.inner_def, RCLike.inner_apply, RCLike.conj_to_real, mul_comm] using hh

lemma L2_pairing_limit_zero {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ} (hg : Tendsto g atTop (𝓝 u))
    (v : Lp ℝ 2 μ)
    (hz : Tendsto (fun i ↦ ∫ x, g i x * v x ∂μ) atTop (𝓝 0)) :
    (∫ x, u x * v x ∂μ) = 0 :=
  tendsto_nhds_unique (L2_pairing_tendsto hg v) hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem restricted_H1_subsequence {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {K : Set X} (hK : IsCompact K)
    (f : ℕ → X → ℝ) (L : ℕ → ℝ≥0) (hf : ∀ i, LipschitzWith (L i) (f i))
    (hfs : ∀ i, Integrable (fun x ↦ f i x ^ 2) μ)
    (hgrad : ∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖ ^ 2) μ)
    {M D : ℝ} (hDnon : 0 ≤ D)
    (hM : ∀ i, (∫ x, f i x ^ 2 ∂μ) ≤ M)
    (hD : ∀ i, (∫ x, ‖fderiv ℝ (f i) x‖ ^ 2 ∂μ) ≤ D) :
    ∃ (u : Lp ℝ 2 (μ.restrict K)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ hmem : ∀ i, MemLp (f i) 2 (μ.restrict K),
        Tendsto (fun i ↦ (hmem (φ i)).toLp (f (φ i))) atTop (𝓝 u) := by
  let η : Measure K := Measure.comap Subtype.val μ
  have hv := measurePreserving_subtype_coe (μa := μ) hK.measurableSet
  change MeasurePreserving ((↑) : K → X) η (μ.restrict K) at hv
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (Measure.map ((↑) : K → X) η) := hv.map_eq.symm ▸ inferInstance
  let : IsFiniteMeasure η := Measure.isFiniteMeasure_of_map hv.measurable.aemeasurable
  obtain ⟨g, φ, hφ, hg⟩ := local_H1_subsequence (μ := μ) (η := η)
    (isometry_subtype_coe.lipschitzWith : LipschitzWith 1 ((↑) : K → X))
    (by rw [hv.map_eq]; exact Measure.restrict_le_self)
    f L hf hfs hgrad hDnon hM hD
  have hmem (i : ℕ) : MemLp (f i) 2 (μ.restrict K) :=
    (MemLp.mono_measure Measure.restrict_le_self)
      ((memLp_two_iff_integrable_sq (hf i).continuous.aestronglyMeasurable).mpr (hfs i))
  let F : ℕ → Lp ℝ 2 (μ.restrict K) := fun i ↦ (hmem i).toLp (f i)
  let G : ℕ → Lp ℝ 2 η := fun i ↦ (BoundedContinuousFunction.toLp 2 η ℝ)
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun y : K ↦ f i y, (hf i).continuous.comp continuous_subtype_val⟩)
  let T := Lp.compMeasurePreserving ((↑) : K → X) hv (E := ℝ) (p := 2)
  have he (i : ℕ) : T (F i) = G i := by
    apply Lp.ext
    have hi := (hmem i).coeFn_toLp
    have hi' : ∀ᵐ (x : K) ∂η, F i (x : X) = f i (x : X) := by
      apply ae_of_ae_map (μ := η) (p := fun x : X ↦ F i x = f i x)
        hv.measurable.aemeasurable
      rw [hv.map_eq]
      exact hi
    filter_upwards [Lp.coeFn_compMeasurePreserving (F i) hv, hi',
      BoundedContinuousFunction.coeFn_toLp 2 η ℝ
        (BoundedContinuousFunction.mkOfCompact
          ⟨fun y : K ↦ f i y, (hf i).continuous.comp continuous_subtype_val⟩)] with x hx hi hxG
    exact hx.trans (hi.trans hxG.symm)
  have hdist (i j : ℕ) : dist (F i) (F j) = dist (G i) (G j) := by
    rw [← he i, ← he j]
    exact ((Lp.isometry_compMeasurePreserving hv).dist_eq _ _).symm
  have hc : CauchySeq (fun i ↦ F (φ i)) := by
    have hg' : Tendsto (fun i ↦ G (φ i)) atTop (𝓝 g) := hg
    have hcg := Metric.cauchySeq_iff.mp hg'.cauchySeq
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hcg ε hε
    exact ⟨N, fun m hm n hn ↦ by rw [hdist]; exact hN m hm n hn⟩
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨u, φ, hφ, hmem, hu⟩

end CubicTorus

end
end

end

end OAI
