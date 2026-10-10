import OAI.Geometry.Perimeter.Regularity.C1MinRegularTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary
open ContinuousLinearMap

theorem gradient_contDiff {n : ℕ} {u : Euc n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (gradient u) := by
  exact (InnerProductSpace.toDual ℝ (Euc n)).symm.contDiff.comp
    (hu.fderiv_right (by simp))

theorem gradient_hasCompactSupport {n : ℕ} {u : Euc n → ℝ}
    (hu : HasCompactSupport u) : HasCompactSupport (gradient u) := by
  exact (hu.fderiv ℝ).comp_left (map_zero _)

theorem integral_mul_divergence_eq_neg_inner_gradient {n : ℕ} {u : Euc n → ℝ}
    {V : Euc n → Euc n} (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V) :
    (∫ x, u x * divergence V x) = - ∫ x, inner ℝ (gradient u x) (V x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → Euc n → ℝ := fun i x ↦ inner ℝ (b i) (V x)
  have hv : ∀ i, ContDiff ℝ ∞ (v i) := fun i ↦ (innerSL ℝ (b i)).contDiff.comp hV
  have hcv : ∀ i, HasCompactSupport (v i) := fun i ↦ hcV.comp_left (by simp)
  have hdv : ∀ i x, fderiv ℝ (v i) x (b i) =
      inner ℝ (b i) (fderiv ℝ V x (b i)) := by
    intro i x
    have h := ((innerSL ℝ (b i)).hasFDerivAt.comp x
      (hV.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L (b i)) h
  have hdi : ∀ i, Continuous (fun x ↦ fderiv ℝ u x (b i)) := fun i ↦
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdvi : ∀ i, Continuous (fun x ↦ fderiv ℝ (v i) x (b i)) := fun i ↦
    ((hv i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hInt1 : ∀ i, Integrable (fun x ↦ fderiv ℝ u x (b i) * v i x) volume := fun i ↦
    ((hdi i).mul (hv i).continuous).integrable_of_hasCompactSupport (hcv i).mul_left
  have hInt2 : ∀ i, Integrable (fun x ↦ u x * fderiv ℝ (v i) x (b i)) volume := fun i ↦
    (hu.continuous.mul (hdvi i)).integrable_of_hasCompactSupport hcu.mul_right
  have hparts : ∀ i, (∫ x, u x * fderiv ℝ (v i) x (b i)) =
      -∫ x, fderiv ℝ u x (b i) * v i x := by
    intro i
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hInt1 i) (hInt2 i)
      ((hu.continuous.mul (hv i).continuous).integrable_of_hasCompactSupport hcu.mul_right)
      (fun x _ ↦ hu.differentiable (by simp) x)
      (fun x _ ↦ (hv i).differentiable (by simp) x)
  calc
    (∫ x, u x * divergence V x) = ∫ x, ∑ i, u x * fderiv ℝ (v i) x (b i) := by
      congr 1
      funext x
      simp only [divergence, hdv, Finset.mul_sum, b]
    _ = ∑ i, ∫ x, u x * fderiv ℝ (v i) x (b i) := integral_finsetSum _ (fun i _ ↦ hInt2 i)
    _ = -(∑ i, ∫ x, fderiv ℝ u x (b i) * v i x) := by simp only [hparts, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, fderiv ℝ u x (b i) * v i x) := by
      rw [integral_finsetSum _ (fun i _ ↦ hInt1 i)]
    _ = -(∫ x, inner ℝ (gradient u x) (V x)) := by
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro x
      simp only [← inner_gradient_left, v]
      exact b.sum_inner_mul_inner _ _

def gradientDualTest {n : ℕ} (u : Euc n → ℝ) (ε : ℝ) (x : Euc n) : Euc n :=
  -(Real.sqrt (ε ^ 2 + ‖gradient u x‖ ^ 2))⁻¹ • gradient u x

theorem gradientDualTest_contDiff {n : ℕ} {u : Euc n → ℝ}
    (hu : ContDiff ℝ ∞ u) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (gradientDualTest u ε) := by
  have hg := gradient_contDiff hu
  have hp : ∀ x, 0 < ε ^ 2 + ‖gradient u x‖ ^ 2 := fun x ↦
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg _)
  exact (((contDiff_const.add (hg.norm_sq ℝ)).sqrt (fun x ↦ (hp x).ne')).inv
    (fun x ↦ (Real.sqrt_pos.2 (hp x)).ne')).neg.smul hg

theorem gradientDualTest_hasCompactSupport {n : ℕ} {u : Euc n → ℝ}
    (hcu : HasCompactSupport u) (ε : ℝ) : HasCompactSupport (gradientDualTest u ε) := by
  change HasCompactSupport ((fun x ↦ -(Real.sqrt (ε ^ 2 + ‖gradient u x‖ ^ 2))⁻¹) • gradient u)
  exact (gradient_hasCompactSupport hcu).smul_left

theorem gradientDualTest_norm_le {n : ℕ} (u : Euc n → ℝ) {ε : ℝ}
    (hε : 0 < ε) (x : Euc n) : ‖gradientDualTest u ε x‖ ≤ 1 := by
  have hp : 0 < ε ^ 2 + ‖gradient u x‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg _)
  have hs : ‖gradient u x‖ ≤ Real.sqrt (ε ^ 2 + ‖gradient u x‖ ^ 2) := by
    rw [Real.le_sqrt (norm_nonneg _) hp.le]
    nlinarith [sq_nonneg ε]
  simp only [gradientDualTest, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [inv_mul_eq_div, div_le_one (Real.sqrt_pos.2 hp)]
  exact hs

theorem integral_norm_gradient_le_of_test_bound {n : ℕ} {u : Euc n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) {P : ℝ}
    (hbound : ∀ V : Euc n → Euc n, PerimeterAdmissible univ V →
      (∫ x, u x * divergence V x) ≤ P) :
    (∫ x, ‖gradient u x‖) ≤ P := by
  let ε : ℕ → ℝ := fun j ↦ 1 / (j + 1 : ℝ)
  have hε : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  let f : ℕ → Euc n → ℝ := fun j x ↦
    ‖gradient u x‖ ^ 2 / Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2)
  have hg := (gradient_contDiff hu).continuous
  have hgi : Integrable (fun x ↦ ‖gradient u x‖) volume :=
    (hg.integrable_of_hasCompactSupport (gradient_hasCompactSupport hcu)).norm
  have hf0 : ∀ j x, 0 ≤ f j x := by intro j x; exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hfle : ∀ j x, f j x ≤ ‖gradient u x‖ := by
    intro j x
    have hp : 0 < ε j ^ 2 + ‖gradient u x‖ ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos (hε j)) (sq_nonneg _)
    have hs : ‖gradient u x‖ ≤ Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2) := by
      rw [Real.le_sqrt (norm_nonneg _) hp.le]
      nlinarith [sq_nonneg (ε j)]
    exact (div_le_iff₀ (Real.sqrt_pos.2 hp)).2 (by nlinarith [norm_nonneg (gradient u x)])
  have hfcont : ∀ j, Continuous (f j) := by
    intro j
    exact (hg.norm.pow 2).div ((continuous_const.add (hg.norm.pow 2)).sqrt)
      (fun x ↦ (Real.sqrt_pos.2
        (add_pos_of_pos_of_nonneg (sq_pos_of_pos (hε j)) (sq_nonneg _))).ne')
  have hflim : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 ‖gradient u x‖) := by
    intro x
    have hlim : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
    by_cases hx : ‖gradient u x‖ = 0
    · simp [f, hx]
    · have hden := ((hlim.pow 2).add_const (‖gradient u x‖ ^ 2)).sqrt
      have hden' : Tendsto (fun j ↦ Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2))
          atTop (𝓝 ‖gradient u x‖) := by
        simpa [Real.sqrt_sq (norm_nonneg _)] using hden
      have hh := (tendsto_const_nhds (x := ‖gradient u x‖ ^ 2)).div hden' hx
      have heq : ‖gradient u x‖ ^ 2 / ‖gradient u x‖ = ‖gradient u x‖ := by
        rw [pow_two, mul_div_cancel_right₀ _ hx]
      change Tendsto (fun j ↦ ‖gradient u x‖ ^ 2 / Real.sqrt (ε j ^ 2 + ‖gradient u x‖ ^ 2))
        atTop (𝓝 (‖gradient u x‖ ^ 2 / ‖gradient u x‖)) at hh
      rw [heq] at hh
      exact hh
  have hlim : Tendsto (fun j ↦ ∫ x, f j x) atTop (𝓝 (∫ x, ‖gradient u x‖)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ ‖gradient u x‖)
      (fun j ↦ (hfcont j).aestronglyMeasurable)
      hgi (fun j ↦ ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 j x)] using hfle j x)
      (ae_of_all _ hflim)
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  let V := gradientDualTest u (ε j)
  have hV : PerimeterAdmissible univ V := ⟨gradientDualTest_contDiff hu (hε j),
    gradientDualTest_hasCompactSupport hcu _, subset_univ _, gradientDualTest_norm_le u (hε j)⟩
  have heq : (∫ x, u x * divergence V x) = ∫ x, f j x := by
    rw [integral_mul_divergence_eq_neg_inner_gradient hu hcu hV.1 hV.2.1, ← integral_neg]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [V, gradientDualTest, inner_smul_right, real_inner_self_eq_norm_sq,
      f, mul_neg, neg_neg, div_eq_mul_inv, mul_comm]
  rw [← heq]
  exact hbound V hV

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
open scoped Convolution

theorem indicator_one_integrable_compact {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hb : Bornology.IsBounded E) :
    Integrable (E.indicator (fun _ ↦ (1 : ℝ))) volume ∧
      HasCompactSupport (E.indicator (fun _ ↦ (1 : ℝ))) := by
  have hfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hb.isCompact_closure.measure_ne_top
    (measure_mono subset_closure)
  refine ⟨(integrable_indicator_iff hE).2 (integrableOn_const hfin), ?_⟩
  apply hb.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  by_contra hn
  exact hx (indicator_of_notMem hn _)

theorem c1Mollify_indicator_gradient_le_perimeter {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hb : Bornology.IsBounded E) (hP : perimeter E univ ≠ ⊤)
    (j : ℕ) :
    (∫⁻ x, ‖fderiv ℝ (c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j) x‖ₑ) ≤
      perimeter E univ := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  let u := c1Mollify χ j
  obtain ⟨hχ, hcχ⟩ := indicator_one_integrable_compact hE hb
  have hu : ContDiff ℝ ∞ u :=
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed hχ.locallyIntegrable
  have hcu : HasCompactSupport u := c1Mollify_hasCompactSupport hcχ j
  have hgrad : (∫ x, ‖gradient u x‖) ≤ (perimeter E univ).toReal := by
    apply integral_norm_gradient_le_of_test_bound hu hcu
    intro V hV
    exact indicator_convolution_variation_le hE hP
      (c1Mollifier j).continuous_normed
      ((c1Mollifier j).continuous_normed.integrable_of_hasCompactSupport
        (c1Mollifier j).hasCompactSupport_normed)
      (c1Mollifier j).nonneg_normed (c1Mollifier j).integral_normed hV
  have hnorm : ∀ x, ‖gradient u x‖ = ‖fderiv ℝ u x‖ := fun x ↦
    (InnerProductSpace.toDual ℝ (Euc n)).symm.norm_map _
  calc
    (∫⁻ x, ‖fderiv ℝ u x‖ₑ) = ∫⁻ x, ENNReal.ofReal ‖gradient u x‖ := by
      apply lintegral_congr
      intro x
      rw [hnorm, ofReal_norm]
    _ = ENNReal.ofReal (∫ x, ‖gradient u x‖) :=
      (ofReal_integral_eq_lintegral_ofReal
        ((gradient_contDiff hu).continuous.integrable_of_hasCompactSupport
          (gradient_hasCompactSupport hcu)).norm (ae_of_all _ fun x ↦ norm_nonneg _)).symm
    _ ≤ ENNReal.ofReal (perimeter E univ).toReal := ENNReal.ofReal_le_ofReal hgrad
    _ = perimeter E univ := ENNReal.ofReal_toReal hP

theorem raw_perimeter_isoperimetric {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) {E : Set (Euc n)}
    (hE : MeasurableSet E) (hb : Bornology.IsBounded E) :
    volume E ≤ (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p : ℝ≥0∞) *
      (perimeter E univ) ^ p := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  obtain ⟨hχ, hcχ⟩ := indicator_one_integrable_compact hE hb
  let u : ℕ → Euc n → ℝ := c1Mollify χ
  have hu : ∀ j, ContDiff ℝ ∞ (u j) := fun j ↦
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed hχ.locallyIntegrable
  have hcu : ∀ j, HasCompactSupport (u j) := c1Mollify_hasCompactSupport hcχ
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun j ↦ u j x) atTop (𝓝 (χ x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      c1Mollifier_radius_tendsto (K := 2) _ hχ.locallyIntegrable
    apply Eventually.of_forall
    intro j
    dsimp [c1Mollifier]
    linarith
  have hSob : ∀ j, (∫⁻ x, ‖u j x‖ₑ ^ p) ≤
      (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p : ℝ≥0∞) *
        (perimeter E univ) ^ p := by
    intro j
    have hs := lintegral_pow_le_pow_lintegral_fderiv volume
      ((hu j).of_le (by simp)) (hcu j) (by simpa using hp)
    apply hs.trans
    gcongr
    · exact hp.symm.pos.le
    by_cases hP : perimeter E univ = ⊤
    · rw [hP]; exact le_top
    · exact c1Mollify_indicator_gradient_le_perimeter hE hb hP j
  have hlp : ∀ᵐ x ∂volume, Tendsto (fun j ↦ ‖u j x‖ₑ ^ p) atTop (𝓝 (‖χ x‖ₑ ^ p)) := by
    filter_upwards [hlim] with x hx
    exact ENNReal.continuous_rpow_const.continuousAt.tendsto.comp hx.enorm
  calc
    volume E = ∫⁻ x, ‖χ x‖ₑ ^ p := by
      have heq : (fun x ↦ ‖χ x‖ₑ ^ p) = E.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
        funext x
        by_cases hx : x ∈ E
        · simp [χ, hx]
        · simp [χ, hx, ENNReal.zero_rpow_of_pos hp.symm.pos]
      rw [heq, lintegral_indicator hE]
      simp
    _ = ∫⁻ x, liminf (fun j ↦ ‖u j x‖ₑ ^ p) atTop := by
      apply lintegral_congr_ae
      filter_upwards [hlp] with x hx using hx.liminf_eq.symm
    _ ≤ liminf (fun j ↦ ∫⁻ x, ‖u j x‖ₑ ^ p) atTop :=
      lintegral_liminf_le' (fun j ↦ ((hu j).continuous.measurable.enorm.pow_const p).aemeasurable)
    _ ≤ (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p : ℝ≥0∞) *
        (perimeter E univ) ^ p := liminf_le_of_frequently_le (Eventually.of_forall hSob).frequently

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem radial_volume_increment_le {n : ℕ} (E : Set (Euc n)) (c : Euc n)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    volume.real (E ∩ Metric.closedBall c b) - volume.real (E ∩ Metric.closedBall c a) ≤
      (b ^ n - a ^ n) * volume.real (Metric.ball (0 : Euc n) 1) := by
  have hf : volume (E ∩ Metric.closedBall c a) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c a).measure_ne_top
  calc
    _ ≤ volume.real ((E ∩ Metric.closedBall c b) \ (E ∩ Metric.closedBall c a)) :=
      le_measureReal_sdiff hf
    _ ≤ volume.real (Metric.closedBall c b \ Metric.closedBall c a) := by
      apply measureReal_mono
      · intro x hx
        exact ⟨hx.1.2, fun h ↦ hx.2 ⟨hx.1.1, h⟩⟩
      · exact measure_ne_top_of_subset sdiff_subset (isCompact_closedBall c b).measure_ne_top
    _ = _ := volume_real_annulus c ha hab

theorem radial_volume_abs_sub_le {n : ℕ} (E : Set (Euc n)) (c : Euc n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |volume.real (E ∩ Metric.closedBall c b) - volume.real (E ∩ Metric.closedBall c a)| ≤
      |b ^ n - a ^ n| * volume.real (Metric.ball (0 : Euc n) 1) := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (measureReal_mono
        (inter_subset_inter_right E (Metric.closedBall_subset_closedBall hab))
        (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c b).measure_ne_top))),
      abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha hab n))]
    exact radial_volume_increment_le E c ha hab
  · rw [abs_sub_comm (volume.real _), abs_sub_comm (b ^ n)]
    rw [abs_of_nonneg (sub_nonneg.mpr (measureReal_mono
        (inter_subset_inter_right E (Metric.closedBall_subset_closedBall hba))
        (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c a).measure_ne_top))),
      abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hb hba n))]
    exact radial_volume_increment_le E c hb hba

theorem radial_volume_continuousAt {n : ℕ} (E : Set (Euc n)) (c : Euc n)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun s : ℝ ↦ volume.real (E ∩ Metric.closedBall c s)) r := by
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun s : ℝ ↦
    |s ^ n - r ^ n| * volume.real (Metric.ball (0 : Euc n) 1))
  · filter_upwards [lt_mem_nhds hr] with s hs
    simpa only [Real.norm_eq_abs] using radial_volume_abs_sub_le E c hr.le hs.le
  · have ht : ContinuousAt (fun s : ℝ ↦
        |s ^ n - r ^ n| * volume.real (Metric.ball (0 : Euc n) 1)) r := by fun_prop
    simpa using ht.tendsto

theorem exists_controlled_cut_radius {n : ℕ} (E : Set (Euc n)) (c : Euc n)
    {a b D : ℝ} (ha : 0 < a) (hab : a < b)
    (hD : volume.real (E ∩ Metric.closedBall c b) < D * (b - a)) :
    ∃ r ∈ Ico a b, ∀ t ∈ Icc r b,
      volume.real (E ∩ Metric.closedBall c t) - volume.real (E ∩ Metric.closedBall c r) ≤
        D * (t - r) := by
  let F : ℝ → ℝ := fun s ↦ volume.real (E ∩ Metric.closedBall c s)
  have hcont : ContinuousOn (fun s ↦ F s - D * s) (Icc a b) := by
    intro s hs
    exact ((radial_volume_continuousAt E c (ha.trans_le hs.1)).sub
      (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hcont
  have hrb : r < b := by
    by_contra hh
    have heq : r = b := le_antisymm hr.2 (not_lt.mp hh)
    subst r
    have hc := hmax (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    have hn : 0 ≤ F a := ENNReal.toReal_nonneg
    dsimp [F] at hc hn
    nlinarith
  refine ⟨r, ⟨hr.1, hrb⟩, ?_⟩
  intro t ht
  have hc := hmax (show t ∈ Icc a b from ⟨hr.1.trans ht.1, ht.2⟩)
  dsimp [F] at hc
  nlinarith

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem integral_gradient_annularCutoff_in_set_le {n : ℕ} (E : Set (Euc n))
    (c : Euc n) {a b L : ℝ} (ha : 0 < a) (hab : a < b) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) :
    (∫ x in E, ‖gradient (annularCutoff c a b) x‖) ≤
      (2 * L * b / (b ^ 2 - a ^ 2)) *
        volume.real (E ∩ (Metric.closedBall c b \ Metric.closedBall c a)) := by
  let A := Metric.closedBall c b \ Metric.closedBall c a
  have hid : (∫ x in A, ‖gradient (annularCutoff c a b) x‖ ∂volume.restrict E) =
      ∫ x in E, ‖gradient (annularCutoff c a b) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [gradient_annularCutoff_zero ha hab, norm_zero]
    by_cases hh : x ∈ Metric.closedBall c a
    · exact Or.inl hh
    · exact Or.inr (le_of_lt (lt_of_not_ge (fun h ↦ hx ⟨h, hh⟩)))
  rw [← hid, Measure.restrict_restrict (measurableSet_closedBall.diff measurableSet_closedBall)]
  calc
    _ ≤ ‖∫ x in A ∩ E, ‖gradient (annularCutoff c a b) x‖‖ := le_abs_self _
    _ ≤ (2 * L * b / (b ^ 2 - a ^ 2)) * volume.real (A ∩ E) := by
      apply norm_setIntegral_le_of_norm_le_const
        ((measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt
          (isCompact_closedBall c b).measure_lt_top)
      intro x hx
      simpa only [norm_norm] using gradient_annularCutoff_bound ha hab hL hbound x
    _ = _ := by rw [inter_comm]

theorem controlled_radius_gradient_bound {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) {r B D L δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδB : r + 2 * δ ≤ B)
    (hcontrol : ∀ t ∈ Icc r B,
      volume.real (E ∩ Metric.closedBall c t) - volume.real (E ∩ Metric.closedBall c r) ≤
        D * (t - r))
    (hD : 0 ≤ D) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) :
    (∫ x in E, ‖gradient (annularCutoff c (r + δ) (r + 2 * δ)) x‖) ≤ 4 * L * D := by
  have ha : 0 < r + δ := by positivity
  have hab : r + δ < r + 2 * δ := by linarith
  have hden : 0 < (r + 2 * δ) ^ 2 - (r + δ) ^ 2 := by nlinarith
  have hv : volume.real (E ∩ (Metric.closedBall c (r + 2 * δ) \ Metric.closedBall c (r + δ))) ≤
      2 * D * δ := by
    calc
      _ ≤ volume.real ((E ∩ Metric.closedBall c (r + 2 * δ)) \ (E ∩ Metric.closedBall c r)) := by
        apply measureReal_mono
        · intro x hx
          refine ⟨⟨hx.1, hx.2.1⟩, ?_⟩
          intro hh
          exact hx.2.2 (Metric.closedBall_subset_closedBall (by linarith : r ≤ r + δ) hh.2)
        · exact measure_ne_top_of_subset (sdiff_subset.trans inter_subset_right)
            (isCompact_closedBall c (r + 2 * δ)).measure_ne_top
      _ = volume.real (E ∩ Metric.closedBall c (r + 2 * δ)) -
          volume.real (E ∩ Metric.closedBall c r) := by
        exact measureReal_sdiff
          (inter_subset_inter_right E (Metric.closedBall_subset_closedBall (by linarith)))
          (hE.inter measurableSet_closedBall)
          (measure_ne_top_of_subset inter_subset_right
            (isCompact_closedBall c (r + 2 * δ)).measure_ne_top)
      _ ≤ D * ((r + 2 * δ) - r) := hcontrol _ ⟨by linarith, hδB⟩
      _ = _ := by ring
  have hcoef : 2 * L * (r + 2 * δ) / ((r + 2 * δ) ^ 2 - (r + δ) ^ 2) ≤
      2 * L / δ := by
    rw [div_le_div_iff₀ hden hδ]
    nlinarith [mul_pos hL (mul_pos ha hδ)]
  calc
    _ ≤ (2 * L * (r + 2 * δ) / ((r + 2 * δ) ^ 2 - (r + δ) ^ 2)) *
        volume.real (E ∩ (Metric.closedBall c (r + 2 * δ) \ Metric.closedBall c (r + δ))) :=
      integral_gradient_annularCutoff_in_set_le E c ha hab hL hbound
    _ ≤ (2 * L / δ) * (2 * D * δ) :=
      (mul_le_mul_of_nonneg_left hv (by positivity)).trans
        (mul_le_mul_of_nonneg_right hcoef (mul_nonneg (mul_nonneg (by norm_num) hD) hδ.le))
    _ = _ := by field_simp; ring

end RPISingularHarnack

end

end OAI
