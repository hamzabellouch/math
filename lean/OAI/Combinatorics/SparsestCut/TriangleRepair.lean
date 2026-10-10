import OAI.Combinatorics.SparsestCut.ChartAngles

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.TriangleRepair
variable {ι : Type u1} [Fintype ι]
lemma exp_distance_intervalIntegrable {d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) :
    IntervalIntegrable (fun l => Real.exp (-d / l)) volume 0 r := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr]
  apply (integrable_const (1 : ℝ)).mono'
  · exact (Real.measurable_exp.comp (measurable_const.div measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hl.1.le)

lemma min_posSemidef (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (Matrix.of (fun i j => min (u i) (u j))).PosSemidef := by
  classical
  let R : ℝ := ∑ i, u i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => hu i)
  have huR (i : ι) : u i ≤ R := Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)
  let K : ℝ → Matrix ι ι ℝ := fun l => Matrix.of fun i j =>
    (if l ≤ u i then 1 else 0) * (if l ≤ u j then 1 else 0)
  have hk (l : ℝ) : (K l).PosSemidef := by
    convert Matrix.posSemidef_vecMulVec_self_star
      (fun i => if l ≤ u i then (1 : ℝ) else 0) using 1 ; try rfl
  have hki (i j : ι) : (fun l => K l i j) =
      (Set.Iic (min (u i) (u j))).indicator (fun _ => (1 : ℝ)) := by
    funext l
    simp only [K, Matrix.of_apply, Set.indicator_apply, Set.mem_Iic, le_min_iff]
    split_ifs <;> norm_num <;> tauto
  have hi (i j : ι) : IntervalIntegrable (fun l => K l i j) volume 0 R := by
    rw [hki]
    exact ⟨(intervalIntegrable_const (a := 0) (b := R) (c := (1 : ℝ))).1.indicator
      measurableSet_Iic,
      (intervalIntegrable_const (a := 0) (b := R) (c := (1 : ℝ))).2.indicator
      measurableSet_Iic⟩
  have h := integral_posSemidef K hR (fun l _ => hk l) hi
  suffices he : Matrix.of (fun i j => min (u i) (u j)) =
      (fun i j => ∫ l in (0 : ℝ)..R, K l i j) by
    rw [he]
    exact h
  ext i j
  rw [hki]
  change min (u i) (u j) =
    ∫ l in (0 : ℝ)..R, Set.indicator {l | l ≤ min (u i) (u j)} (fun _ => (1 : ℝ)) l
  rw [intervalIntegral.integral_indicator
    (show min (u i) (u j) ∈ Set.Icc 0 R from
      ⟨le_min (hu i) (hu j), (min_le_left _ _).trans (huR i)⟩)]
  simp

lemma abs_sub_sq_hilbert (u : ι → ℝ) :
    ∃ h : ι → EuclideanSpace ℝ ι, ∀ i j, ‖h i - h j‖ ^ 2 = |u i - u j| := by
  let b : ℝ := ∑ i, |u i|
  have hu (i : ι) : 0 ≤ u i + b := by
    have hb : |u i| ≤ b := Finset.single_le_sum (fun j _ => abs_nonneg (u j))
      (Finset.mem_univ i)
    have := neg_abs_le (u i)
    linarith
  obtain ⟨h, hh⟩ := exists_gram (min_posSemidef (fun i => u i + b) hu)
  refine ⟨h, fun i j => ?_⟩
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    hh, hh, hh]
  simp only [Matrix.of_apply, min_self]
  rcases le_total (u i) (u j) with hij | hji
  · rw [min_eq_left (add_le_add_left hij b), abs_of_nonpos (sub_nonpos.mpr hij)]
    ring
  · rw [min_eq_right (add_le_add_left hji b), abs_of_nonneg (sub_nonneg.mpr hji)]
    ring

lemma l1_sq_hilbert {κ : Type u2} [Fintype κ] (x : ι → κ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∃ h : ι → EuclideanSpace ℝ (κ × ι),
      ∀ i j, ‖h i - h j‖ ^ 2 = a * ∑ k, |x i k - x j k| := by
  classical
  choose h hh using fun k => abs_sub_sq_hilbert (fun i => x i k)
  refine ⟨fun i => WithLp.toLp 2 (fun ki => Real.sqrt a * h ki.1 i ki.2), ?_⟩
  intro i j
  rw [EuclideanSpace.norm_sq_eq]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs,
    Fintype.sum_prod_type]
  have hs : ∀ k, ∑ l, (Real.sqrt a * h k i l - Real.sqrt a * h k j l) ^ 2 =
      a * |x i k - x j k| := by
    intro k
    simp_rw [← mul_sub, mul_pow, Real.sq_sqrt ha]
    rw [← Finset.mul_sum, ← hh k i j, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs]
  simp_rw [hs]
  exact (Finset.mul_sum _ _ _).symm

lemma repair_integral_le {d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) :
    (∫ l in (0 : ℝ)..r, 1 - Real.exp (-d / l)) ≤ r := by
  have hi := (intervalIntegrable_const (c := (1 : ℝ))).sub (exp_distance_intervalIntegrable hd hr)
  have h := intervalIntegral.integral_mono_on hr hi
    (intervalIntegrable_const (c := (1 : ℝ))) (fun l _ => by
      have := (Real.exp_pos (-d / l)).le
      linarith)
  simpa using h

lemma repair_integral_local {d r : ℝ} (hd : 0 < d) (hdr : d ≤ r) :
    (∫ l in (0 : ℝ)..r, 1 - Real.exp (-d / l)) ≤
      d * (1 + Real.log (r / d)) := by
  have hr : 0 ≤ r := hd.le.trans hdr
  have hi := (intervalIntegrable_const (c := (1 : ℝ))).sub (exp_distance_intervalIntegrable hd.le hr)
  have hi₀ := (intervalIntegrable_const (c := (1 : ℝ))).sub (exp_distance_intervalIntegrable hd.le hd.le)
  have hi₁ : IntervalIntegrable (fun l => 1 - Real.exp (-d / l)) volume d r :=
    hi.mono_set (by
      rw [Set.uIcc_of_le hdr, Set.uIcc_of_le hr]
      exact Set.Icc_subset_Icc hd.le le_rfl)
  have hn : 0 ∉ Set.uIcc d r := by
    rw [Set.uIcc_of_le hdr]
    exact fun h => (not_le_of_gt hd) h.1
  have hj : IntervalIntegrable (fun l => d * l⁻¹) volume d r :=
    (intervalIntegrable_inv_iff.mpr (Or.inr hn)).const_mul d
  have hbound := intervalIntegral.integral_mono_on hdr hi₁ hj (fun l hl => by
    have he := Real.one_sub_le_exp_neg (d / l)
    rw [← neg_div] at he
    rw [← div_eq_mul_inv]
    linarith)
  rw [intervalIntegral.integral_const_mul, integral_inv hn] at hbound
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₀ hi₁]
  have hfirst := repair_integral_le hd.le hd.le
  linarith

section Charts

variable {κ : Type u3} {H : Type u4} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable def chartKernel (c : ι → κ) (h : ι → H) (l : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if c i = c j then Real.exp (-‖h i - h j‖ ^ 2 / l) else 0

noncomputable def cappedDistance (c : ι → κ) (h : ι → H) (r : ℝ) (i j : ι) : ℝ :=
  if c i = c j then min r (‖h i - h j‖ ^ 2) else r

omit [Fintype κ] in
lemma chartKernel_posSemidef (c : ι → κ) (h : ι → H) {l : ℝ} (hl : 0 ≤ l) :
    (chartKernel c h l).PosSemidef := by
  have hm := (Matrix.PosSemidef.one (n := κ) (R := ℝ)).submatrix c
  rcases hl.eq_or_lt with rfl | hl
  · convert hm using 1
    ext i j
    simp [chartKernel, Matrix.submatrix_apply, Matrix.one_apply]
  · have hg := gaussian_posSemidef h hl
    convert hm.hadamard hg using 1
    ext i j
    change (if c i = c j then _ else 0) =
      (if c i = c j then (1 : ℝ) else 0) * _
    split_ifs <;> simp

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_intervalIntegrable (c : ι → κ) (h : ι → H) {r : ℝ}
    (hr : 0 ≤ r) (i j : ι) :
    IntervalIntegrable (fun l => chartKernel c h l i j) volume 0 r := by
  by_cases hij : c i = c j
  · simpa [chartKernel, hij] using exp_distance_intervalIntegrable (sq_nonneg ‖h i - h j‖) hr
  · simp only [chartKernel, Matrix.of_apply, hij, ite_false]
    exact intervalIntegrable_const

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_nonneg (c : ι → κ) (h : ι → H) (l : ℝ) (i j : ι) :
    0 ≤ chartKernel c h l i j := by
  simp only [chartKernel, Matrix.of_apply]
  split_ifs <;> positivity

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_le_one (c : ι → κ) (h : ι → H) {l : ℝ} (hl : 0 ≤ l) (i j : ι) :
    chartKernel c h l i j ≤ 1 := by
  simp only [chartKernel, Matrix.of_apply]
  split_ifs
  · exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) hl)
  · norm_num

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_self (c : ι → κ) (h : ι → H) (l : ℝ) (i : ι) :
    chartKernel c h l i i = 1 := by simp [chartKernel]

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_symm (c : ι → κ) (h : ι → H) (l : ℝ) (i j : ι) :
    chartKernel c h l i j = chartKernel c h l j i := by
  simp only [chartKernel, Matrix.of_apply, norm_sub_rev (h j) (h i)]
  by_cases hij : c i = c j <;> simp [hij, eq_comm]

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma cappedDistance_nonneg (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r) (i j : ι) :
    0 ≤ cappedDistance c h r i j := by
  simp only [cappedDistance]
  split_ifs
  · exact le_min hr (sq_nonneg _)
  · exact hr

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma cappedDistance_le (c : ι → κ) (h : ι → H) (r : ℝ) (i j : ι) :
    cappedDistance c h r i j ≤ r := by
  simp only [cappedDistance]
  split_ifs
  · exact min_le_left _ _
  · rfl

def ChartTriangle (c : ι → κ) (h : ι → H) : Prop :=
  ∀ i j k, c i = c j → c j = c k →
    ‖h i - h k‖ ^ 2 ≤ ‖h i - h j‖ ^ 2 + ‖h j - h k‖ ^ 2

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_mul_le (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {l : ℝ} (hl : 0 < l) (i j z : ι) :
    chartKernel c h l i z * chartKernel c h l j z ≤ chartKernel c h l i j := by
  by_cases hiz : c i = c z
  · by_cases hjz : c j = c z
    · simp only [chartKernel, Matrix.of_apply, hiz, hjz, ite_true]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hl.le
      have htri := ht i z j hiz hjz.symm
      rw [norm_sub_rev (h z) (h j)] at htri
      linarith
    · simp only [chartKernel, Matrix.of_apply, hjz, ite_false, mul_zero]
      split_ifs <;> positivity
  · simp only [chartKernel, Matrix.of_apply, hiz, ite_false, zero_mul]
    split_ifs <;> positivity

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_le_half (c : ι → κ) (h : ι → H) {r l : ℝ}
    (hl : 0 < l) (i j : ι) (hle : l ≤ cappedDistance c h r i j) :
    chartKernel c h l i j ≤ 1 / 2 := by
  by_cases hij : c i = c j
  · have hd : l ≤ ‖h i - h j‖ ^ 2 := by
      exact le_trans hle (by simp [cappedDistance, hij])
    simp only [chartKernel, Matrix.of_apply, hij, ite_true]
    calc
      Real.exp (-‖h i - h j‖ ^ 2 / l) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ hl).mpr
        linarith
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        have := Real.add_one_le_exp (1 : ℝ)
        norm_num at this ⊢
        exact this
  · simp [chartKernel, hij]

def IsRepairGram (c : ι → κ) (h : ι → H) (r : ℝ)
    (q : ι → EuclideanSpace ℝ ι) : Prop :=
  ∀ i j, ⟪q i, q j⟫_ℝ = 4 * ∫ l in (0 : ℝ)..r, chartKernel c h l i j

omit [Fintype κ] in
lemma exists_repairGram (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r) :
    ∃ q : ι → EuclideanSpace ℝ ι, IsRepairGram c h r q := by
  have hi := integral_posSemidef (chartKernel c h) hr
    (fun l hl => chartKernel_posSemidef c h hl.1) (chartKernel_intervalIntegrable c h hr)
  obtain ⟨q, hq⟩ := exists_gram (hi.smul (by norm_num : (0 : ℝ) ≤ 4))
  exact ⟨q, hq⟩

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_norm_sq (c : ι → κ) (h : ι → H) {r : ℝ}
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i : ι) :
    ‖q i‖ ^ 2 = 4 * r := by
  rw [← real_inner_self_eq_norm_sq, hq]
  simp_rw [chartKernel_self]
  simp

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_distance (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i j : ι) :
    ‖q i - q j‖ ^ 2 = 8 * ∫ l in (0 : ℝ)..r, 1 - chartKernel c h l i j := by
  rw [norm_sub_sq_real, repairGram_norm_sq c h hq, repairGram_norm_sq c h hq, hq,
    intervalIntegral.integral_sub intervalIntegrable_const
      (chartKernel_intervalIntegrable c h hr i j)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  ring

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_distance_le (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i j : ι) :
    ‖q i - q j‖ ^ 2 ≤ 8 * r := by
  rw [repairGram_distance c h hr hq]
  have hi := (intervalIntegrable_const (c := (1 : ℝ))).sub
    (chartKernel_intervalIntegrable c h hr i j)
  have hb := intervalIntegral.integral_mono_on hr hi
    (intervalIntegrable_const (c := (1 : ℝ))) (fun l _ => by
      have := chartKernel_nonneg c h l i j
      linarith)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hb
  linarith

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_local (c : ι → κ) (h : ι → H) {r : ℝ}
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) {i j : ι}
    (hij : c i = c j) (hd : 0 < ‖h i - h j‖ ^ 2) (hdr : ‖h i - h j‖ ^ 2 ≤ r) :
    ‖q i - q j‖ ^ 2 ≤ 8 * ‖h i - h j‖ ^ 2 *
      (1 + Real.log (r / ‖h i - h j‖ ^ 2)) := by
  rw [repairGram_distance c h (hd.le.trans hdr) hq]
  simp only [chartKernel, Matrix.of_apply, hij, ite_true]
  have := repair_integral_local hd hdr
  nlinarith

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_eq_of_zero (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) {i j : ι}
    (hij : c i = c j) (hd : ‖h i - h j‖ ^ 2 = 0) : q i = q j := by
  have hdq := repairGram_distance c h hr hq i j
  simp only [chartKernel, Matrix.of_apply, hij, ite_true, hd, neg_zero, zero_div,
    Real.exp_zero, sub_self, intervalIntegral.integral_zero, mul_zero] at hdq
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdq))

noncomputable def angleIntegrand (c : ι → κ) (h : ι → H) (i j z : ι) (l : ℝ) : ℝ :=
  1 - chartKernel c h l i z - chartKernel c h l j z + chartKernel c h l i j

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma angleIntegrand_integrable (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    (i j z : ι) : IntervalIntegrable (angleIntegrand c h i j z) volume 0 r :=
  (((intervalIntegrable_const (c := (1 : ℝ))).sub (chartKernel_intervalIntegrable c h hr i z)).sub
    (chartKernel_intervalIntegrable c h hr j z)).add (chartKernel_intervalIntegrable c h hr i j)

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_angle (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i j z : ι) :
    ⟪q i - q z, q j - q z⟫_ℝ = 4 * ∫ l in (0 : ℝ)..r, angleIntegrand c h i j z l := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hq, hq, hq, hq]
  simp_rw [chartKernel_self, chartKernel_symm c h _ z j]
  rw [show (fun l => angleIntegrand c h i j z l) =
      (fun l => 1 - chartKernel c h l i z - chartKernel c h l j z +
        chartKernel c h l i j) from rfl]
  rw [intervalIntegral.integral_add
    (((intervalIntegrable_const (c := (1 : ℝ))).sub
      (chartKernel_intervalIntegrable c h hr i z)).sub
      (chartKernel_intervalIntegrable c h hr j z)) (chartKernel_intervalIntegrable c h hr i j)]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_const (c := (1 : ℝ))).sub (chartKernel_intervalIntegrable c h hr i z))
    (chartKernel_intervalIntegrable c h hr j z)]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (chartKernel_intervalIntegrable c h hr i z)]
  ring

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma angleIntegrand_nonneg (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {l : ℝ} (hl : 0 < l) (i j z : ι) : 0 ≤ angleIntegrand c h i j z l := by
  have ha := chartKernel_le_one c h hl.le i z
  have hb := chartKernel_le_one c h hl.le j z
  have hc := chartKernel_mul_le c h ht hl i j z
  have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  dsimp only [angleIntegrand]
  nlinarith

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma angleIntegrand_ge_quarter (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {r l : ℝ} (hl : 0 < l) (i j z : ι)
    (hli : l ≤ cappedDistance c h r i z) (hlj : l ≤ cappedDistance c h r j z) :
    1 / 4 ≤ angleIntegrand c h i j z l := by
  have ha := chartKernel_le_half c h hl i z hli
  have hb := chartKernel_le_half c h hl j z hlj
  have hc := chartKernel_mul_le c h ht hl i j z
  have hp := mul_le_mul
    (show (1 / 2 : ℝ) ≤ 1 - chartKernel c h l i z by linarith)
    (show (1 / 2 : ℝ) ≤ 1 - chartKernel c h l j z by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (show 0 ≤ 1 - chartKernel c h l i z by linarith)
  dsimp only [angleIntegrand]
  nlinarith

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_angle_lower (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {r : ℝ} (hr : 0 ≤ r) {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q)
    (i j z : ι) :
    min (cappedDistance c h r i z) (cappedDistance c h r j z) ≤
      ⟪q i - q z, q j - q z⟫_ℝ := by
  let t := min (cappedDistance c h r i z) (cappedDistance c h r j z)
  have ht₀ : 0 ≤ t := le_min (cappedDistance_nonneg c h hr i z)
    (cappedDistance_nonneg c h hr j z)
  have htr : t ≤ r := (min_le_left _ _).trans (cappedDistance_le c h r i z)
  have hf : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc 0 r)] angleIntegrand c h i j z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    exact angleIntegrand_nonneg c h ht hl.1 i j z
  have hlower := intervalIntegral.integral_mono_ae_restrict ht₀
    (intervalIntegrable_const (c := (1 / 4 : ℝ))) (angleIntegrand_integrable c h ht₀ i j z)
    (show (fun _ => (1 / 4 : ℝ)) ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      angleIntegrand c h i j z from by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with l hl hne
      exact angleIntegrand_ge_quarter c h ht (lt_of_le_of_ne hl.1 (Ne.symm hne)) i j z
        (hl.2.trans (min_le_left _ _)) (hl.2.trans (min_le_right _ _)))
  have hmono := intervalIntegral.integral_mono_interval le_rfl ht₀ htr hf
    (angleIntegrand_integrable c h hr i j z)
  rw [repairGram_angle c h hr hq]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlower
  dsimp only [t] at *
  linarith

omit [Fintype κ] [DecidableEq κ] in

lemma chart_l1_sq_hilbert {ξ : Type u5} [Fintype ξ] (c : ι → κ) (x : ι → ξ → ℝ)
    (a : κ → ℝ) (ha : ∀ s, 0 ≤ a s) :
    ∃ h : ι → EuclideanSpace ℝ (ξ × ι),
      (∀ i j, c i = c j → ‖h i - h j‖ ^ 2 = a (c i) * ∑ k, |x i k - x j k|) ∧
      ChartTriangle c h := by
  obtain ⟨g, hg⟩ := l1_sq_hilbert x (by norm_num : (0 : ℝ) ≤ 1)
  let h : ι → EuclideanSpace ℝ (ξ × ι) := fun i => Real.sqrt (a (c i)) • g i
  have hh (i j : ι) (hc : c i = c j) :
      ‖h i - h j‖ ^ 2 = a (c i) * ∑ k, |x i k - x j k| := by
    dsimp only [h]
    rw [← hc, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (ha (c i)), hg]
    ring
  refine ⟨h, hh, fun i j k hij hjk => ?_⟩
  rw [hh i k (hij.trans hjk), hh i j hij, hh j k hjk, ← hij, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (ha (c i))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun l _ => abs_sub_le (x i l) (x j l) (x k l))

lemma sum_sq_hilbert {E : Type u6} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ι → E) (q : ι → H) :
    ∃ z : ι → EuclideanSpace ℝ ι, ∀ i j,
      ‖z i - z j‖ ^ 2 = ‖P i - P j‖ ^ 2 + ‖q i - q j‖ ^ 2 := by
  obtain ⟨z, hz⟩ := exists_gram ((gram_posSemidef P).add (gram_posSemidef q))
  refine ⟨z, fun i j => ?_⟩
  simp only [norm_sub_sq_real]
  simp only [← real_inner_self_eq_norm_sq, hz, Matrix.add_apply, Matrix.of_apply]
  ring

lemma angle_triangle_slack (x y z : H) :
    ‖x - y‖ ^ 2 + ‖z - y‖ ^ 2 - ‖x - z‖ ^ 2 = 2 * ⟪x - y, z - y⟫_ℝ := by
  have he : x - z = (x - y) - (z - y) := by abel
  rw [he, norm_sub_sq_real (x - y) (z - y)]
  ring

omit [Fintype κ] in

theorem triangle_repair {E : Type u7} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h) {r : ℝ} (hr : 0 < r)
    (P : ι → E)
    (hP : ∀ i j z, -min (cappedDistance c h r i z) (cappedDistance c h r j z) ≤
      ⟪P i - P z, P j - P z⟫_ℝ) :
    ∃ q z : ι → EuclideanSpace ℝ ι,
      IsRepairGram c h r q ∧
      (∀ i j, ‖z i - z j‖ ^ 2 = ‖P i - P j‖ ^ 2 + ‖q i - q j‖ ^ 2) ∧
      (∀ i j k, ‖z i - z k‖ ^ 2 ≤ ‖z i - z j‖ ^ 2 + ‖z j - z k‖ ^ 2) ∧
      (∀ i j, ‖q i - q j‖ ^ 2 = 8 * ∫ l in (0 : ℝ)..r, 1 - chartKernel c h l i j) ∧
      (∀ i j, ‖q i - q j‖ ^ 2 ≤ 8 * r) ∧
      (∀ i j, c i = c j → 0 < ‖h i - h j‖ ^ 2 → ‖h i - h j‖ ^ 2 ≤ r →
        ‖q i - q j‖ ^ 2 ≤ 8 * ‖h i - h j‖ ^ 2 * (1 + Real.log (r / ‖h i - h j‖ ^ 2))) ∧
      (∀ i j, c i = c j → ‖h i - h j‖ ^ 2 = 0 → q i = q j) := by
  obtain ⟨q, hq⟩ := exists_repairGram c h hr.le
  obtain ⟨z, hz⟩ := sum_sq_hilbert P q
  refine ⟨q, z, hq, hz, ?_, repairGram_distance c h hr.le hq,
    repairGram_distance_le c h hr.le hq,
    fun _ _ hc hd hdr => repairGram_local c h hq hc hd hdr,
    fun _ _ hc hd => repairGram_eq_of_zero c h hr.le hq hc hd⟩
  intro i j k
  rw [hz, hz, hz]
  have hp := hP i k j
  have hqangle := repairGram_angle_lower c h ht hr.le hq i k j
  have hpAngle := angle_triangle_slack (P i) (P j) (P k)
  have hqAngle := angle_triangle_slack (q i) (q j) (q k)
  rw [norm_sub_rev (P k) (P j)] at hpAngle
  rw [norm_sub_rev (q k) (q j)] at hqAngle
  linarith

end Charts

end UniformSparsestCut.TriangleRepair

end

end OAI
