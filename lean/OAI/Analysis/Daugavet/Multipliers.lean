import OAI.Analysis.Daugavet.SliceCharacterization

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

def scale (p : ℝ) : ℝ := (p - 1) / p

def multiplier (p : ℝ) (v : unitInterval) : ℝ := scale p * (v : ℝ) ^ (-1 / p)

lemma scale_pos {p : ℝ} (hp : 1 < p) : 0 < scale p := by
  dsimp [scale]; positivity

lemma scale_lt_one {p : ℝ} (hp : 1 < p) : scale p < 1 := by
  unfold scale
  rw [div_lt_one (by linarith : 0 < p)]
  linarith

lemma multiplier_nonneg {p : ℝ} (hp : 1 < p) (v : unitInterval) :
    0 ≤ multiplier p v := mul_nonneg (scale_pos hp).le (Real.rpow_nonneg v.property.1 _)

lemma measurable_multiplier (p : ℝ) : Measurable (multiplier p) := by
  unfold multiplier
  fun_prop

lemma integrable_multiplier {p : ℝ} (hp : 1 < p) :
    Integrable (multiplier p) (volume : Measure unitInterval) := by
  have hp0 : 0 < p := by linarith
  have hexp : -1 < -1 / p := by rw [lt_div_iff₀ hp0]; linarith
  have hi : IntegrableOn (fun x : ℝ => x ^ (-1 / p)) (Icc 0 1) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr
      ((intervalIntegral.intervalIntegrable_rpow' hexp).1)
  have hc := (unitInterval.measurePreserving_coe.integrable_comp hi.aestronglyMeasurable).mpr hi
  exact hc.const_mul (scale p)

lemma integral_multiplier {p : ℝ} (hp : 1 < p) :
    ∫ v : unitInterval, multiplier p v = 1 := by
  have hp0 : 0 < p := by linarith
  have hexp : -1 < -1 / p := by rw [lt_div_iff₀ hp0]; linarith
  unfold multiplier
  rw [integral_const_mul]
  change scale p * (∫ x : Icc (0:ℝ) 1, (x:ℝ) ^ (-1 / p)) = 1
  rw [integral_subtype measurableSet_Icc (fun x : ℝ => x ^ (-1 / p)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_rpow (Or.inl hexp)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : -1 / p + 1 ≠ 0)]
  dsimp [scale]
  field_simp [hp0.ne', show p - 1 ≠ 0 by linarith, show -1 + p ≠ 0 by linarith]
  ring

lemma multiplier_tail {p u : ℝ} (hp : 1 < p) (hu : scale p ≤ u) :
    (volume : Measure unitInterval).real {v | u < multiplier p v} = (scale p / u) ^ p := by
  have hs : 0 < scale p := scale_pos hp
  have hu0 : 0 < u := hs.trans_le hu
  have hp0 : 0 < p := by linarith
  let q := (scale p / u) ^ p
  have hq : 0 < q := Real.rpow_pos_of_pos (div_pos hs hu0) _
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact Real.rpow_le_one (by positivity) ((div_le_one hu0).mpr hu) hp0.le
  let a : unitInterval := ⟨q, hq.le, hq1⟩
  have hqpow : q ^ (-1 / p) = u / scale p := by
    dsimp [q]
    rw [← Real.rpow_mul (div_pos hs hu0).le]
    have hm : p * (-1 / p) = -1 := by field_simp
    rw [hm, Real.rpow_neg_one, inv_div]
  have haeq : {v : unitInterval | u < multiplier p v} =ᵐ[volume] Iio a := by
    have hne : ∀ᵐ v : unitInterval, v ≠ 0 := volume.ae_ne 0
    filter_upwards [hne] with v hv
    have hv0 : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1 (by
      intro heq; apply hv; apply Subtype.ext; exact heq.symm)
    apply propext
    change (u < scale p * (v : ℝ) ^ (-1 / p)) ↔ (v : ℝ) < q
    have hueq : u = scale p * q ^ (-1 / p) := by rw [hqpow]; field_simp
    rw [hueq, mul_lt_mul_iff_right₀ hs,
      Real.rpow_lt_rpow_iff_of_neg hq hv0 (div_neg_of_neg_of_pos (by norm_num) hp0)]
  rw [measureReal_congr haeq, measureReal_def, unitInterval.volume_Iio,
    ENNReal.toReal_ofReal hq.le]

lemma multiplier_tail_le {p u : ℝ} (hp : 1 < p) (hu : 0 < u) :
    (volume : Measure unitInterval).real {v | u < multiplier p v} ≤ (scale p / u) ^ p := by
  by_cases hs : scale p ≤ u
  · exact le_of_eq (multiplier_tail hp hs)
  · have hsu : 1 ≤ (scale p / u) ^ p := Real.one_le_rpow
      ((le_div_iff₀ hu).mpr (by linarith : 1 * u ≤ scale p)) (by linarith)
    exact (measureReal_le_one).trans hsu

abbrev pairedMeasure : Measure (unitInterval × unitInterval) :=
  (volume : Measure unitInterval).prod volume

def difference (p : ℝ) (v : unitInterval × unitInterval) : ℝ :=
  multiplier p v.1 - multiplier p v.2

lemma measurable_difference (p : ℝ) : Measurable (difference p) :=
  ((measurable_multiplier p).comp measurable_fst).sub
    ((measurable_multiplier p).comp measurable_snd)

lemma integrable_difference {p : ℝ} (hp : 1 < p) :
    Integrable (difference p) pairedMeasure := by
  exact ((measurePreserving_fst.integrable_comp
    (integrable_multiplier hp).aestronglyMeasurable).mpr (integrable_multiplier hp)).sub
    ((measurePreserving_snd.integrable_comp
    (integrable_multiplier hp).aestronglyMeasurable).mpr (integrable_multiplier hp))

lemma difference_symmetric (p : ℝ) :
    IdentDistrib (difference p) (fun v => -difference p v) pairedMeasure pairedMeasure := by
  have hcomp : (fun v => -difference p v) = difference p ∘ Prod.swap := by
    funext v
    simp [difference, sub_eq_add_neg, add_comm]
  refine ⟨(measurable_difference p).aemeasurable,
    (measurable_difference p).neg.aemeasurable, ?_⟩
  rw [hcomp, ← Measure.map_map (measurable_difference p) measurable_swap, Measure.prod_swap]

lemma difference_tail_upper {p u : ℝ} (hp : 1 < p) (hu : 0 < u) :
    pairedMeasure.real {v | u < |difference p v|} ≤ 2 * (scale p / u) ^ p := by
  let A := {v : unitInterval | u < multiplier p v}
  have hsub : {v | u < |difference p v|} ⊆ (A ×ˢ univ) ∪ (univ ×ˢ A) := by
    intro v hv
    change u < |multiplier p v.1 - multiplier p v.2| at hv
    by_contra hn
    have he : multiplier p v.1 ≤ u ∧ multiplier p v.2 ≤ u := by
      simpa [A] using hn
    have h1 := multiplier_nonneg hp v.1
    have h2 := multiplier_nonneg hp v.2
    have hb : |multiplier p v.1 - multiplier p v.2| ≤ u :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  calc
    _ ≤ pairedMeasure.real ((A ×ˢ univ) ∪ (univ ×ˢ A)) := measureReal_mono hsub
    _ ≤ pairedMeasure.real (A ×ˢ univ) + pairedMeasure.real (univ ×ˢ A) := measureReal_union_le _ _
    _ = 2 * (volume : Measure unitInterval).real A := by
      rw [measureReal_prod_prod, measureReal_prod_prod]
      simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (multiplier_tail_le hp hu) (by norm_num)

lemma difference_tail_lower {p u : ℝ} (hp : 1 < p) (hpmax : p ≤ 3 / 2)
    (hu : scale p ≤ u) :
    (1 / 18) * (scale p / u) ^ p ≤ pairedMeasure.real {v | u < |difference p v|} := by
  have hs : 0 < scale p := scale_pos hp
  have hu0 : 0 < u := hs.trans_le hu
  have hp0 : 0 < p := by linarith
  let B := {v : unitInterval | u + 2 * scale p < multiplier p v}
  let C := {v : unitInterval | 2 * scale p < multiplier p v}ᶜ
  have hsub : B ×ˢ C ⊆ {v | u < |difference p v|} := by
    intro v hv
    have hB : u + 2 * scale p < multiplier p v.1 := hv.1
    have hC : multiplier p v.2 ≤ 2 * scale p := le_of_not_gt hv.2
    have hdiff : u < difference p v := by dsimp [difference]; linarith
    exact hdiff.trans_le (le_abs_self _)
  have hB : (volume : Measure unitInterval).real B = (scale p / (u + 2 * scale p)) ^ p :=
    multiplier_tail hp (by linarith)
  have hC : (1 / 2 : ℝ) ≤ (volume : Measure unitInterval).real C := by
    have heq : scale p / (2 * scale p) = (1 / 2 : ℝ) := by field_simp
    have hpow : (1 / 2 : ℝ) ^ p ≤ 1 / 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hp.le
    have hvol : (volume : Measure unitInterval).real univ = 1 := by simp
    dsimp [C]
    rw [measureReal_compl (measurableSet_lt measurable_const (measurable_multiplier p)),
      hvol, multiplier_tail hp (by linarith), heq]
    linarith
  have hB9 : (scale p / u) ^ p ≤ 9 * (volume : Measure unitInterval).real B := by
    rw [hB]
    have hd : (scale p / u) / 3 ≤ scale p / (u + 2 * scale p) := by
      rw [div_div]
      apply (div_le_div_iff₀ (by positivity : 0 < u * 3) (by positivity)).mpr
      nlinarith
    have hpow := Real.rpow_le_rpow (show 0 ≤ (scale p / u) / 3 by positivity) hd hp0.le
    rw [Real.div_rpow (by positivity) (by norm_num)] at hpow
    have h3 : (3:ℝ) ^ p ≤ 9 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
        (show p ≤ 2 by linarith)
      norm_num at h
      exact h
    have hin := (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) p)).mp hpow
    have hmul := mul_le_mul_of_nonneg_right h3
      (Real.rpow_nonneg (by positivity : 0 ≤ scale p / (u + 2 * scale p)) p)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hC
    (measureReal_nonneg : 0 ≤ (volume : Measure unitInterval).real B)
  have hm := measureReal_mono (μ := pairedMeasure) hsub
  rw [measureReal_prod_prod] at hm
  nlinarith

end ExactModuli.KW

end

end OAI
