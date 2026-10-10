import OAI.Geometry.CylinderCovering.Rational.CeilingIntegralDefinitions
import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Rational.CeilingIntegral
import OAI.Geometry.CylinderCovering.Rational.Domain

namespace OAI

open Set MeasureTheory
open scoped Topology

noncomputable section
namespace SlopeRational.DomainArea

def box (a b c e : ℝ) : Set Plane :=
  {z | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c e}

lemma box_isCompact (a b c e : ℝ) : IsCompact (box a b c e) := by
  have hc : IsClosed (box a b c e) := by
    exact ((isClosed_le (f := fun _ : Plane => a) (g := fun z => z 0)
      (by fun_prop) (by fun_prop)).inter
      (isClosed_le (f := fun z : Plane => z 0) (g := fun _ => b)
        (by fun_prop) (by fun_prop))).inter
      ((isClosed_le (f := fun _ : Plane => c) (g := fun z => z 1)
        (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => z 1) (g := fun _ => e)
          (by fun_prop) (by fun_prop)))
  apply (isCompact_closedBall (0 : Plane) (|a| + |b| + |c| + |e|)).of_isClosed_subset hc
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hx : |z 0| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_le_abs a, abs_nonneg b, hz.1.1]
    · linarith [le_abs_self b, abs_nonneg a, hz.1.2]
  have hy : |z 1| ≤ |c| + |e| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_le_abs c, abs_nonneg e, hz.2.1]
    · linarith [le_abs_self e, abs_nonneg c, hz.2.2]
  exact (RuledApproximation.plane_norm_le_sum z).trans (by linarith)

lemma box_volume {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e) :
    volume.real (box a b c e) = (b - a) * (e - c) := by
  rw [RuledApproximation.plane_volume_vertical_interval
    (box_isCompact a b c e).measurableSet (box_isCompact a b c e).measure_lt_top.ne
    (s := Icc a b) (l := fun _ => c) (u := fun _ => e) measurableSet_Icc
    (by intro z; rfl)]
  simp [max_eq_left (sub_nonneg.mpr hce), integral_const,
    Real.volume_real_Icc_of_le hab, smul_eq_mul]

def centralBand (f : ℝ → ℝ) : Set Plane :=
  {z | |z 0| ≤ (1 / 4 : ℝ) ∧ -f (z 0) ≤ z 1 ∧ z 1 ≤ 1 / 2 - 2 * |z 0|}

lemma centralBand_isClosed {f : ℝ → ℝ} (hf : Continuous f) : IsClosed (centralBand f) := by
  exact (isClosed_le (f := fun z : Plane => |z 0|) (g := fun _ => (1 / 4 : ℝ))
    (by fun_prop) (by fun_prop)).inter
    ((isClosed_le (f := fun z : Plane => -f (z 0)) (g := fun z => z 1)
      (by fun_prop) (by fun_prop)).inter
      (isClosed_le (f := fun z : Plane => z 1) (g := fun z => 1 / 2 - 2 * |z 0|)
        (by fun_prop) (by fun_prop)))

lemma centralBand_subset_box {f : ℝ → ℝ} {M : ℝ}
    (hfM : ∀ x, |x| ≤ (1 / 4 : ℝ) → f x ≤ M) :
    centralBand f ⊆ box (-1 / 4) (1 / 4) (-M) (1 / 2) := by
  intro z hz
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mem_Icc, neg_div] using abs_le.mp hz.1
  · linarith [hfM (z 0) hz.1, hz.2.1]
  · linarith [hz.2.2, abs_nonneg (z 0)]

lemma centralBand_isCompact {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hfM : ∀ x, |x| ≤ (1 / 4 : ℝ) → f x ≤ M) :
    IsCompact (centralBand f) :=
  (box_isCompact (-1 / 4) (1 / 4) (-M) (1 / 2)).of_isClosed_subset
    (centralBand_isClosed hf) (centralBand_subset_box hfM)

lemma triangle_height_integral :
    (∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), (1 / 2 : ℝ) - 2 * |y|) = 1 / 8 := by
  have hc : Continuous (fun y : ℝ => (1 / 2 : ℝ) - 2 * |y|) := by fun_prop
  have hn : (∫ y in (-1 / 4 : ℝ)..0, (1 / 2 : ℝ) - 2 * |y|) =
      ∫ y in (-1 / 4 : ℝ)..0, (1 / 2 : ℝ) + 2 * y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by norm_num)] at hy
    dsimp only
    rw [abs_of_nonpos hy.2]
    ring
  have hp : (∫ y in (0 : ℝ)..(1 / 4 : ℝ), (1 / 2 : ℝ) - 2 * |y|) =
      ∫ y in (0 : ℝ)..(1 / 4 : ℝ), (1 / 2 : ℝ) - 2 * y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by norm_num)] at hy
    dsimp only
    rw [abs_of_nonneg hy.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1 / 4) 0) (hc.intervalIntegrable 0 (1 / 4)), hn, hp,
    intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_id, integral_id]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  · exact continuous_const.intervalIntegrable _ _
  · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _
  · exact (continuous_const.mul continuous_id).intervalIntegrable _ _

lemma centralBand_volume {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hf0 : ∀ x, |x| ≤ (1 / 4 : ℝ) → 0 ≤ f x)
    (hfM : ∀ x, |x| ≤ (1 / 4 : ℝ) → f x ≤ M) :
    volume.real (centralBand f) = (1 / 8 : ℝ) +
      ∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), f y := by
  have hc := centralBand_isCompact hf hfM
  have hv := RuledApproximation.plane_volume_vertical_interval hc.measurableSet
    hc.measure_lt_top.ne (s := Icc (-1 / 4 : ℝ) (1 / 4 : ℝ))
    (l := fun y => -f y) (u := fun y => 1 / 2 - 2 * |y|) measurableSet_Icc
    (by
      intro z
      simp only [centralBand, mem_ofPred_eq, mem_Icc, abs_le, neg_div])
  have he : volume.real (centralBand f) =
      ∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), (1 / 2 : ℝ) - 2 * |y| + f y := by
    rw [hv, intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    have hyabs : |y| ≤ (1 / 4 : ℝ) := by
      apply abs_le.mpr
      simpa only [mem_Icc, neg_div] using hy
    have hpos : 0 ≤ (1 / 2 : ℝ) - 2 * |y| - -f y := by
      linarith [hf0 y hyabs]
    dsimp only
    rw [max_eq_left hpos]
    ring
  rw [he, intervalIntegral.integral_add, triangle_height_integral]
  · exact (show Continuous (fun y : ℝ => (1 / 2 : ℝ) - 2 * |y|) by fun_prop).intervalIntegrable _ _
  · exact hf.intervalIntegrable _ _

lemma wing_volumes {M : ℝ} (hM : 0 ≤ M) :
    volume.real (box (-1 / 4 - M / 2) (-1 / 4) (-M) 0) = M ^ 2 / 2 ∧
    volume.real (box (1 / 4) (1 / 4 + M / 2) (-M) 0) = M ^ 2 / 2 := by
  constructor
  · rw [box_volume (by linarith) (by linarith)]
    ring
  · rw [box_volume (by linarith) (by linarith)]
    ring

lemma area_sandwich {S : Set Plane} {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : Continuous f)
    (hf0 : ∀ x, |x| ≤ (1 / 4 : ℝ) → 0 ≤ f x)
    (hfM : ∀ x, |x| ≤ (1 / 4 : ℝ) → f x ≤ M)
    (hCS : centralBand f ⊆ S)
    (hSU : S ⊆ centralBand f ∪
      (box (-1 / 4 - M / 2) (-1 / 4) (-M) 0 ∪
        box (1 / 4) (1 / 4 + M / 2) (-M) 0)) :
    0 ≤ volume.real S - ((1 / 8 : ℝ) + ∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), f y) ∧
    volume.real S - ((1 / 8 : ℝ) + ∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), f y) ≤ M ^ 2 := by
  have hC := centralBand_isCompact hf hfM
  have hL := box_isCompact (-1 / 4 - M / 2) (-1 / 4) (-M) 0
  have hR := box_isCompact (1 / 4) (1 / 4 + M / 2) (-M) 0
  have hU := hC.union (hL.union hR)
  have hSfin : volume S ≠ ⊤ := measure_ne_top_of_subset hSU hU.measure_lt_top.ne
  have hlo := measureReal_mono hCS hSfin
  have hup := measureReal_mono (μ := volume) hSU hU.measure_lt_top.ne
  have hsum := measureReal_union_le (μ := volume) (centralBand f)
    (box (-1 / 4 - M / 2) (-1 / 4) (-M) 0 ∪ box (1 / 4) (1 / 4 + M / 2) (-M) 0)
  have hw := measureReal_union_le (μ := volume)
    (box (-1 / 4 - M / 2) (-1 / 4) (-M) 0) (box (1 / 4) (1 / 4 + M / 2) (-M) 0)
  rw [centralBand_volume hf hf0 hfM] at hlo hsum
  rw [(wing_volumes hM).1, (wing_volumes hM).2] at hw
  constructor <;> linarith

lemma ceiling_coefficients_bounds {d : ℝ} (hd : 0 ≤ d) :
    (0 ≤ alpha d ∧ alpha d ≤ 1) ∧
    (0 ≤ ceilingConstant d ∧ ceilingConstant d ≤ 1) ∧
    (0 ≤ ceilingQuadratic d ∧ ceilingQuadratic d ≤ 1) := by
  have hden : 0 < (1 / 2 : ℝ) + d := by linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · unfold alpha
    positivity
  · unfold alpha
    exact (div_le_one (by positivity)).mpr (by linarith)
  · unfold ceilingConstant
    positivity
  · unfold ceilingConstant
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg d]
  · unfold ceilingQuadratic
    positivity
  · unfold ceilingQuadratic
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg d]

lemma ceilingPolynomial_continuous (d : ℝ) : Continuous (ceilingPolynomial d) := by
  unfold ceilingPolynomial ceilingCoefficient
  fun_prop

lemma ceilingPolynomial_bounds {d y : ℝ} (hd : 0 ≤ d) (hy : |y| ≤ (3 / 8 : ℝ)) :
    0 ≤ ceilingPolynomial d y ∧ ceilingPolynomial d y ≤ 1 := by
  rcases ceiling_coefficients_bounds hd with ⟨hα, hc, hb⟩
  have hy2 : y ^ 2 ≤ (1 / 4 : ℝ) := by
    have hsq := (sq_le_sq₀ (abs_nonneg y) (show 0 ≤ (3 / 8 : ℝ) by norm_num)).mpr hy
    rw [sq_abs] at hsq
    nlinarith
  have hC0 : 0 ≤ ceilingCoefficient d y := by
    unfold ceilingCoefficient
    exact add_nonneg hc.1 (mul_nonneg hb.1 (sq_nonneg y))
  have hC1 : ceilingCoefficient d y ≤ (5 / 4 : ℝ) := by
    unfold ceilingCoefficient
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (sq_nonneg y)]
  have hprod : alpha d * ceilingCoefficient d y ≤ (5 / 4 : ℝ) := by
    have h := mul_le_mul hα.2 hC1 hC0 (show (0 : ℝ) ≤ 1 by norm_num)
    simpa using h
  unfold ceilingPolynomial
  constructor
  · exact mul_nonneg (mul_nonneg hα.1 hC0) (sq_nonneg y)
  · have h := mul_le_mul hprod hy2 (sq_nonneg y) (show (0 : ℝ) ≤ 5 / 4 by norm_num)
    nlinarith

lemma labelDomain_horizontal_bound {d ε q : ℝ} {z : Plane}
    (hz : z ∈ labelDomain d ε q) : |z 0| ≤ (3 / 8 : ℝ) := by
  have hw := hz.1
  change 2 * |z 0| ≤ 1 / 2 - z 1 at hw
  linarith [hz.2.1]

lemma padding_integral (d ε q : ℝ) :
    (∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), ε ^ 2 * ceilingPolynomial d y + q) =
      ε ^ 2 * ceilingIntegral d + q / 2 := by
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    change ε ^ 2 * ceilingIntegral d + ((1 / 4 : ℝ) - -1 / 4) * q = _
    ring
  · exact (continuous_const.mul (ceilingPolynomial_continuous d)).intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _

theorem labelDomain_area_remainder {d ε q : ℝ} (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hsmall : ε ^ 2 + q ≤ (1 / 4 : ℝ)) :
    0 ≤ volume.real (labelDomain d ε q) -
      ((1 / 8 : ℝ) + ε ^ 2 * ceilingIntegral d + q / 2) ∧
    volume.real (labelDomain d ε q) -
      ((1 / 8 : ℝ) + ε ^ 2 * ceilingIntegral d + q / 2) ≤ (ε ^ 2 + q) ^ 2 := by
  let f : ℝ → ℝ := fun y => ε ^ 2 * ceilingPolynomial d y + q
  let M : ℝ := ε ^ 2 + q
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hf : Continuous f := continuous_const.mul (ceilingPolynomial_continuous d) |>.add continuous_const
  have hf0 : ∀ y, |y| ≤ (3 / 8 : ℝ) → 0 ≤ f y := by
    intro y hy
    have hP := (ceilingPolynomial_bounds hd hy).1
    dsimp [f]
    positivity
  have hfM : ∀ y, |y| ≤ (3 / 8 : ℝ) → f y ≤ M := by
    intro y hy
    have hP := (ceilingPolynomial_bounds hd hy).2
    dsimp [f, M]
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hP)]
  have hCS : centralBand f ⊆ labelDomain d ε q := by
    intro z hz
    have hfz := hfM (z 0) (by linarith [hz.1])
    refine ⟨?_, ?_, ?_⟩
    · change 2 * |z 0| ≤ 1 / 2 - z 1
      linarith [hz.2.2]
    · have hMz : M ≤ (1 / 4 : ℝ) := hsmall
      linarith [hz.2.1]
    ·
      have h := hz.2.1
      dsimp [f] at h
      linarith
  have hSU : labelDomain d ε q ⊆ centralBand f ∪
      (box (-1 / 4 - M / 2) (-1 / 4) (-M) 0 ∪
        box (1 / 4) (1 / 4 + M / 2) (-M) 0) := by
    intro z hz
    have hy := labelDomain_horizontal_bound hz
    have hw := hz.1
    change 2 * |z 0| ≤ 1 / 2 - z 1 at hw
    have hcut : -f (z 0) ≤ z 1 := by
      dsimp [f]
      linarith [hz.2.2]
    by_cases hmid : |z 0| ≤ (1 / 4 : ℝ)
    · exact Or.inl ⟨hmid, hcut, by linarith⟩
    · have hout : (1 / 4 : ℝ) < |z 0| := lt_of_not_ge hmid
      have hT0 : z 1 ≤ 0 := by linarith
      have hTM : -M ≤ z 1 := by linarith [hfM (z 0) hy]
      have hyM : |z 0| ≤ (1 / 4 : ℝ) + M / 2 := by linarith
      apply Or.inr
      by_cases hneg : z 0 ≤ 0
      · rw [abs_of_nonpos hneg] at hout hyM
        exact Or.inl ⟨⟨by linarith, by linarith⟩, hTM, hT0⟩
      · rw [abs_of_nonneg (le_of_not_ge hneg)] at hout hyM
        exact Or.inr ⟨⟨by linarith, by linarith⟩, hTM, hT0⟩
  have h := area_sandwich hM hf
    (fun y hy => hf0 y (by linarith)) (fun y hy => hfM y (by linarith)) hCS hSU
  dsimp only [f, M] at h
  rw [padding_integral] at h
  simpa only [add_assoc] using h

lemma unperturbed_domain (d : ℝ) :
    labelDomain d 0 0 = wedge ∩ {z : Plane | 0 ≤ z 1} := by
  ext z
  simp only [labelDomain, mem_ofPred_eq, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    neg_zero, zero_mul, sub_zero, mem_inter_iff]
  constructor
  · rintro ⟨hw, _, hT⟩
    exact ⟨hw, hT⟩
  · rintro ⟨hw, hT⟩
    exact ⟨hw, by linarith, hT⟩

lemma unperturbed_domain_area {d : ℝ} (hd : 0 ≤ d) :
    volume.real (labelDomain d 0 0) = (1 / 8 : ℝ) := by
  have h := labelDomain_area_remainder (ε := 0) hd (le_refl (0 : ℝ)) (by norm_num)
  norm_num at h
  linarith

lemma unperturbed_subset {d ε q : ℝ} (hd : 0 ≤ d) (hq : 0 ≤ q) :
    labelDomain d 0 0 ⊆ labelDomain d ε q := by
  intro z hz
  have hT : 0 ≤ z 1 := by simpa using hz.2.2
  have hP := (ceilingPolynomial_bounds hd (labelDomain_horizontal_bound hz)).1
  refine ⟨hz.1, hz.2.1, ?_⟩
  have hn := mul_nonneg (sq_nonneg ε) hP
  linarith

lemma added_domain_area {d ε q : ℝ} (hd : 0 ≤ d) (hq : 0 ≤ q) :
    volume.real (labelDomain d ε q \ labelDomain d 0 0) =
      volume.real (labelDomain d ε q) - (1 / 8 : ℝ) := by
  rw [measureReal_sdiff (unperturbed_subset hd hq)
    (labelDomain_measurableSet d 0 0) (labelDomain_volume_ne_top d ε q),
    unperturbed_domain_area hd]

lemma ceilingIntegral_le_half {d : ℝ} (hd : 0 ≤ d) :
    ceilingIntegral d ≤ (1 / 2 : ℝ) := by
  have h : (∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), ceilingPolynomial d y) ≤
      ∫ y in (-1 / 4 : ℝ)..(1 / 4 : ℝ), (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((ceilingPolynomial_continuous d).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro y hy
    apply (ceilingPolynomial_bounds hd ?_).2
    apply abs_le.mpr
    constructor <;> linarith [hy.1, hy.2]
  norm_num [intervalIntegral.integral_const] at h
  simpa only [ceilingIntegral, neg_div] using h

theorem labelDomain_area_bounds {d ε q : ℝ} (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hsmall : ε ^ 2 + q ≤ (1 / 4 : ℝ)) :
    volume.real (labelDomain d ε q) ≤ (3 / 8 : ℝ) ∧
    volume.real (labelDomain d ε q \ labelDomain d 0 0) ≤ ε ^ 2 + q := by
  have hr := (labelDomain_area_remainder hd hq hsmall).2
  have hJ := ceilingIntegral_le_half hd
  have hJmul := mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hJ)
  have hM : 0 ≤ ε ^ 2 + q := by positivity
  have hMsq := mul_nonneg hM (sub_nonneg.mpr hsmall)
  rw [added_domain_area hd hq]
  constructor <;> nlinarith

theorem labelDomain_area_remainder_quadratic {d ε q Q : ℝ}
    (hd : 0 ≤ d) (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hqQ : q ≤ Q * ε ^ 2)
    (hsmall : ε ^ 2 + q ≤ (1 / 4 : ℝ)) :
    |volume.real (labelDomain d ε q) -
      ((1 / 8 : ℝ) + ε ^ 2 * ceilingIntegral d + q / 2)| ≤
        (1 + Q) ^ 2 * ε ^ 4 ∧
    volume.real (labelDomain d ε q \ labelDomain d 0 0) ≤ (1 + Q) * ε ^ 2 := by
  have hr := labelDomain_area_remainder hd hq hsmall
  have hM : ε ^ 2 + q ≤ (1 + Q) * ε ^ 2 := by nlinarith
  constructor
  · rw [abs_of_nonneg hr.1]
    apply hr.2.trans
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ ε ^ 2 + q) (by positivity : 0 ≤ (1 + Q) * ε ^ 2)).mpr hM
    nlinarith [hs]
  · exact (labelDomain_area_bounds hd hq hsmall).2.trans hM

lemma quadratic_padding_small {ε q Q : ℝ} (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hεsmall : ε ≤ 1 / (4 * (1 + Q))) (hqQ : q ≤ Q * ε ^ 2) :
    ε ^ 2 + q ≤ (1 / 4 : ℝ) := by
  have hden : 0 < 4 * (1 + Q) := by positivity
  have hδ : 1 / (4 * (1 + Q)) ≤ (1 : ℝ) :=
    (div_le_one hden).mpr (by linarith)
  have hε1 := hεsmall.trans hδ
  have hs : ε ^ 2 ≤ ε := by nlinarith [mul_nonneg hε (sub_nonneg.mpr hε1)]
  have hlin := (le_div_iff₀ hden).mp hεsmall
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1 + Q by positivity)
  nlinarith

theorem labelDomain_area_estimates_small {d ε q Q : ℝ}
    (hd : 0 ≤ d) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hεsmall : ε ≤ 1 / (4 * (1 + Q))) (hq : 0 ≤ q) (hqQ : q ≤ Q * ε ^ 2) :
    |volume.real (labelDomain d ε q) -
      ((1 / 8 : ℝ) + ε ^ 2 * ceilingIntegral d + q / 2)| ≤
        (1 + Q) ^ 2 * ε ^ 4 ∧
    volume.real (labelDomain d ε q) ≤ (3 / 8 : ℝ) ∧
    volume.real (labelDomain d ε q \ labelDomain d 0 0) ≤ (1 + Q) * ε ^ 2 := by
  have hs := quadratic_padding_small hQ hε hεsmall hqQ
  have hr := labelDomain_area_remainder_quadratic hd hq hQ hqQ hs
  exact ⟨hr.1, (labelDomain_area_bounds hd hq hs).1, hr.2⟩

end SlopeRational.DomainArea

end

end OAI
