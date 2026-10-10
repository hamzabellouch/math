import OAI.Analysis.Daugavet.Multipliers

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe u_1 uIota

namespace ExactModuli.KW

section TailMoments
variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measurable_real_tail (X : Ω → ℝ) : Measurable (fun t : ℝ => μ.real {ω | t < X ω}) := by
  apply Antitone.measurable
  intro a b hab
  exact measureReal_mono (fun _ ht => hab.trans_lt ht)

/-- The bounded weighted layer-cake identity used for truncation variances. -/
lemma integral_min_abs_sq {X : Ω → ℝ} (hX : Measurable X) {u : ℝ} (hu : 0 < u) :
    ∫ ω, (min |X ω| u) ^ 2 ∂μ =
      ∫ t in Ioc 0 u, 2 * t * μ.real {ω | t < |X ω|} := by
  let m := fun ω => min |X ω| u
  have hm : Measurable m := hX.abs.min measurable_const
  have hm0 : ∀ ω, 0 ≤ m ω := fun ω => le_min (abs_nonneg _) hu.le
  have hinner : ∀ ω, (∫ t in (0:ℝ)..m ω, 2 * t) = m ω ^ 2 := by
    intro ω
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hlay := lintegral_comp_eq_lintegral_meas_lt_mul μ (ae_of_all _ hm0) hm.aemeasurable
    (fun t ht => (continuous_id.intervalIntegrable 0 t).const_mul (2:ℝ))
    (show ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ 2 * t from
      (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => mul_nonneg (by norm_num) (le_of_lt ht)))
  change (∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..m ω, 2 * t) ∂μ) = _ at hlay
  simp only [id_eq] at hlay
  simp_rw [hinner] at hlay
  have hright : (∫⁻ t in Ioi (0:ℝ), μ {ω | t < m ω} * ENNReal.ofReal (2 * t)) =
      ∫⁻ t in Ioc 0 u, ENNReal.ofReal (2 * t * μ.real {ω | t < |X ω|}) := by
    calc
      _ = ∫⁻ t in Ioi (0:ℝ), (Iio u).indicator
          (fun t => ENNReal.ofReal (2 * t * μ.real {ω | t < |X ω|})) t := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change μ {ω | t < m ω} * ENNReal.ofReal (2 * t) = _
        have ht0 : 0 < t := ht
        by_cases htu : t < u
        · rw [Set.indicator_of_mem (show t ∈ Iio u from htu)]
          have he : {ω | t < m ω} = {ω | t < |X ω|} := by
            ext ω
            simp [m, htu]
          rw [he, ENNReal.ofReal_mul (show 0 ≤ 2 * t by positivity), measureReal_def,
            ENNReal.ofReal_toReal (measure_ne_top _ _)]
          exact mul_comm _ _
        · have he : {ω | t < m ω} = ∅ := by
            ext ω
            simp [m, htu]
          rw [he, measure_empty, zero_mul, Set.indicator_of_notMem (show t ∉ Iio u from htu)]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Ioi, restrict_Ioo_eq_restrict_Ioc]
  rw [hright] at hlay
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => sq_nonneg (m ω)))
      (hm.pow_const 2).aestronglyMeasurable]
  rw [hlay]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num) ht.1.le) measureReal_nonneg
  · exact ((measurable_const.mul measurable_id).mul
      (measurable_real_tail (fun ω => |X ω|))).aestronglyMeasurable

/-- A truncated symmetric summand has second moment controlled using its tail. -/
lemma integral_min_sq_tail_bound {X : Ω → ℝ} (hX : Measurable X)
    {p C u : ℝ} (_hp : 0 < p) (hp2 : p < 2) (_hC : 0 ≤ C) (hu : 0 < u)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < |X ω|} ≤ C * t ^ (-p)) :
    ∫ ω, (min |X ω| u) ^ 2 ∂μ ≤ (2 * C / (2 - p)) * u ^ (2 - p) := by
  rw [integral_min_abs_sq hX hu]
  have hexp : -1 < 1 - p := by linarith
  have hi : IntegrableOn (fun t : ℝ => 2 * C * t ^ (1 - p)) (Ioc 0 u) volume :=
    (intervalIntegral.intervalIntegrable_rpow' hexp).1.const_mul _
  have hle : (∫ t in Ioc 0 u, 2 * t * μ.real {ω | t < |X ω|}) ≤
      ∫ t in Ioc 0 u, 2 * C * t ^ (1 - p) := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (mul_nonneg (by norm_num) ht.1.le) measureReal_nonneg
    · exact hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hbound := mul_le_mul_of_nonneg_left (htail t ht0) (show 0 ≤ 2 * t by positivity)
      convert hbound using 1
      rw [Real.rpow_sub ht0, Real.rpow_one, Real.rpow_neg ht0.le]
      ring
  refine hle.trans_eq ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hu.le,
    integral_rpow (Or.inl hexp), Real.zero_rpow (by linarith : 1 - p + 1 ≠ 0)]
  have he : 1 - p + 1 = 2 - p := by ring
  rw [he]
  ring

def hardTruncate (u x : ℝ) : ℝ := if |x| ≤ u then x else 0

lemma measurable_hardTruncate (u : ℝ) : Measurable (hardTruncate u) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

lemma hardTruncate_neg (u x : ℝ) : hardTruncate u (-x) = -hardTruncate u x := by
  simp only [hardTruncate, abs_neg]
  split_ifs <;> simp

lemma abs_hardTruncate_le {u : ℝ} (hu : 0 ≤ u) (x : ℝ) : |hardTruncate u x| ≤ u := by
  unfold hardTruncate
  split_ifs with h
  · exact h
  · simpa using hu

lemma hardTruncate_sq_le_min_sq {u : ℝ} (_hu : 0 ≤ u) (x : ℝ) :
    (hardTruncate u x) ^ 2 ≤ (min |x| u) ^ 2 := by
  unfold hardTruncate
  split_ifs with h
  · simp [min_eq_left h, sq_abs]
  · simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact sq_nonneg _

omit [IsProbabilityMeasure μ] in
lemma integral_hardTruncate_zero [IsProbabilityMeasure μ] {X : Ω → ℝ} {u : ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ) :
    ∫ ω, hardTruncate u (X ω) ∂μ = 0 := by
  have h := (hsym.comp (measurable_hardTruncate u)).integral_eq
  change (∫ ω, hardTruncate u (X ω) ∂μ) = ∫ ω, hardTruncate u (-X ω) ∂μ at h
  simp_rw [hardTruncate_neg] at h
  rw [integral_neg] at h
  linarith

lemma hardTruncate_memLp {X : Ω → ℝ} (hX : Measurable X) {u : ℝ} (hu : 0 ≤ u) :
    MemLp (fun ω => hardTruncate u (X ω)) 2 μ := by
  exact MemLp.of_bound ((measurable_hardTruncate u).comp hX).aestronglyMeasurable u
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using abs_hardTruncate_le hu (X ω)))

lemma hardTruncate_variance_bound {X : Ω → ℝ} (hX : Measurable X)
    {p C u : ℝ} (hp : 0 < p) (hp2 : p < 2) (hC : 0 ≤ C) (hu : 0 < u)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < |X ω|} ≤ C * t ^ (-p)) :
    variance (fun ω => hardTruncate u (X ω)) μ ≤ (2 * C / (2 - p)) * u ^ (2 - p) := by
  refine (variance_le_expectation_sq
    ((measurable_hardTruncate u).comp hX).aestronglyMeasurable).trans ?_
  refine le_trans ?_ (integral_min_sq_tail_bound hX hp hp2 hC hu htail)
  apply integral_mono_of_nonneg (ae_of_all _ (fun ω => sq_nonneg _))
  · refine (integrable_const (u ^ 2)).mono' ((hX.abs.min measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hmin0 : 0 ≤ min |X ω| u := le_min (abs_nonneg _) hu.le
    have hminu := min_le_right |X ω| u
    nlinarith
  · exact ae_of_all _ (fun ω => hardTruncate_sq_le_min_sq hu.le (X ω))

/-- Truncation, the union bound, and Chebyshev, uniformly in the number of summands. -/
lemma independent_symmetric_sum_tail {ι : Type uIota} [Fintype ι]
    (X : ι → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ)
    {p : ℝ} (hp : 0 < p) (hp2 : p < 2) (C : ι → ℝ) (hC : ∀ j, 0 ≤ C j)
    (htail : ∀ j t, 0 < t → μ.real {ω | t < |X j ω|} ≤ C j * t ^ (-p))
    {u : ℝ} (hu : 0 < u) :
    μ.real {ω | u < |∑ j, X j ω|} ≤
      (1 + 2 / (2 - p)) * (∑ j, C j) * u ^ (-p) := by
  classical
  let T := fun j ω => hardTruncate u (X j ω)
  have hT : ∀ j, MemLp (T j) 2 μ := fun j => hardTruncate_memLp (hX j) hu.le
  have hTi : iIndepFun T μ := hind.comp (fun _ => hardTruncate u) (fun _ => measurable_hardTruncate u)
  have hTzero : ∀ j, ∫ ω, T j ω ∂μ = 0 := fun j => integral_hardTruncate_zero (hsym j)
  let S := fun ω => ∑ j, T j ω
  have hSmem : MemLp S 2 μ := by
    exact memLp_finsetSum _ (fun j _ => hT j)
  have hSzero : ∫ ω, S ω ∂μ = 0 := by
    rw [show S = fun ω => ∑ j, T j ω from rfl, integral_finsetSum _
      (fun j _ => (hT j).integrable (by norm_num))]
    simp [hTzero]
  have hvar : variance S μ = ∑ j, variance (T j) μ := by
    have hSf : S = ∑ j, T j := by ext ω; simp [S]
    rw [hSf]
    exact (IndepFun.variance_sum (s := Finset.univ) (fun j _ => hT j)
        (fun i _ j _ hij => hTi.indepFun hij))
  have hvarbound : variance S μ ≤ (2 / (2 - p)) * (∑ j, C j) * u ^ (2 - p) := by
    rw [hvar]
    calc
      _ ≤ ∑ j, (2 * C j / (2 - p)) * u ^ (2 - p) :=
        Finset.sum_le_sum (fun j _ => hardTruncate_variance_bound (hX j) hp hp2 (hC j) hu (htail j))
      _ = ∑ j, (2 / (2 - p) * C j) * u ^ (2 - p) := by
        apply Finset.sum_congr rfl; intro j hj; ring
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcheb : μ.real {ω | u < |S ω|} ≤ variance S μ / u ^ 2 := by
    have h := meas_ge_le_variance_div_sq hSmem hu
    rw [hSzero] at h
    simp only [sub_zero] at h
    exact (measureReal_mono (fun ω (hω : u < |S ω|) => hω.le)).trans
      (ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg u)) h)
  have hpow : u ^ (2 - p) / u ^ (2:ℕ) = u ^ (-p) := by
    rw [Real.rpow_sub hu, Real.rpow_two, Real.rpow_neg hu.le]
    field_simp
  have hSbound : μ.real {ω | u < |S ω|} ≤ (2 / (2 - p)) * (∑ j, C j) * u ^ (-p) := by
    refine hcheb.trans ?_
    have h := div_le_div_of_nonneg_right hvarbound (sq_nonneg u)
    simpa only [mul_div_assoc, hpow] using h
  have hunion : μ.real (⋃ j, {ω | u < |X j ω|}) ≤ (∑ j, C j) * u ^ (-p) := by
    refine (measureReal_iUnion_fintype_le _).trans ?_
    calc
      _ ≤ ∑ j, C j * u ^ (-p) := Finset.sum_le_sum (fun j _ => htail j u hu)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hsub : {ω | u < |∑ j, X j ω|} ⊆ (⋃ j, {ω | u < |X j ω|}) ∪ {ω | u < |S ω|} := by
    intro ω hω
    by_cases he : ∃ j, u < |X j ω|
    · left; exact mem_iUnion.mpr he
    · right
      have hx : ∀ j, hardTruncate u (X j ω) = X j ω := by
        intro j
        exact ite_eq_left (le_of_not_gt (fun hj => he ⟨j, hj⟩))
      simpa [S, T, hx] using hω
  have hb := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  linarith

end TailMoments

end ExactModuli.KW

end

end OAI
