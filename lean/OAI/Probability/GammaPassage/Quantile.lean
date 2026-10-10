import OAI.Probability.GammaPassage.CDF
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable def gammaQuantileReal (shape rate : ℝ) (hs : 0 < shape) (hr : 0 < rate)
    (u : ℝ) : ℝ :=
  if h : 0 ≤ u ∧ u < 1 then
    Classical.choose (ExistsUnique.exists (gamma_cdf_existsUnique hs hr h.1 h.2))
  else 0

lemma gammaQuantileReal_spec {shape rate u : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (hu : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ gammaQuantileReal shape rate hs hr u ∧
      cdf (gammaMeasure shape rate) (gammaQuantileReal shape rate hs hr u) = u := by
  simp only [gammaQuantileReal, dite_eq_left (show 0 ≤ u ∧ u < 1 from ⟨hu, hu1⟩)]
  exact Classical.choose_spec (ExistsUnique.exists (gamma_cdf_existsUnique hs hr hu hu1))

lemma gammaQuantileReal_nonneg {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (u : ℝ) : 0 ≤ gammaQuantileReal shape rate hs hr u := by
  by_cases hu : 0 ≤ u ∧ u < 1
  · exact (gammaQuantileReal_spec hs hr hu.1 hu.2).1
  · simp [gammaQuantileReal, hu]

lemma gammaQuantileReal_le_iff {shape rate u x : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (hu : 0 ≤ u) (hu1 : u < 1) (hx : 0 ≤ x) :
    gammaQuantileReal shape rate hs hr u ≤ x ↔ u ≤ cdf (gammaMeasure shape rate) x := by
  have hq := gammaQuantileReal_spec hs hr hu hu1
  constructor
  · intro h
    rw [← hq.2]
    exact monotone_cdf _ h
  · intro h
    by_contra hn
    have hh := gamma_cdf_strictMonoOn hs hr hx hq.1 (lt_of_not_ge hn)
    rw [hq.2] at hh
    exact (not_lt_of_ge h) hh

lemma gammaQuantileReal_zero {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    gammaQuantileReal shape rate hs hr 0 = 0 := by
  apply le_antisymm _ (gammaQuantileReal_nonneg hs hr 0)
  apply (gammaQuantileReal_le_iff hs hr (le_refl 0) zero_lt_one (le_refl 0)).mpr
  exact cdf_nonneg _ _

lemma gammaQuantileReal_measurable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    Measurable (gammaQuantileReal shape rate hs hr) := by
  apply measurable_of_Iic
  intro x
  by_cases hx : 0 ≤ x
  · have he : gammaQuantileReal shape rate hs hr ⁻¹' Iic x =
        (Ico (0 : ℝ) 1)ᶜ ∪ (Ico 0 1 ∩ Iic (cdf (gammaMeasure shape rate) x)) := by
      ext u
      by_cases hu : 0 ≤ u ∧ u < 1
      · simp only [mem_preimage, mem_Iic, mem_union, mem_compl_iff, mem_Ico, hu,
          not_true_eq_false, false_or, mem_inter_iff, true_and]
        exact gammaQuantileReal_le_iff hs hr hu.1 hu.2 hx
      · simp [gammaQuantileReal, hu, hx]
    rw [he]
    exact measurableSet_Ico.compl.union (measurableSet_Ico.inter measurableSet_Iic)
  · have he : gammaQuantileReal shape rate hs hr ⁻¹' Iic x = ∅ := by
      ext u
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hx) (gammaQuantileReal_nonneg hs hr u))
    rw [he]
    exact MeasurableSet.empty

/-- Lebesgue probability on the closed unit interval. -/
noncomputable def unitUniform : Measure ℝ := volume.restrict (Icc 0 1)

lemma unitUniform_eq_Ico : unitUniform = volume.restrict (Ico (0 : ℝ) 1) :=
  restrict_Ico_eq_restrict_Icc.symm

instance unitUniform_probability : IsProbabilityMeasure unitUniform where
  measure_univ := by simp [unitUniform, Real.volume_Icc]

lemma gammaQuantileReal_map {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    Measure.map (gammaQuantileReal shape rate hs hr) unitUniform = gammaMeasure shape rate := by
  let := isProbabilityMeasure_gammaMeasure hs hr
  have hmeas := gammaQuantileReal_measurable hs hr
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hmeas measurableSet_Iic, unitUniform_eq_Ico,
    Measure.restrict_apply (hmeas measurableSet_Iic)]
  by_cases hx : 0 ≤ x
  · have he : (gammaQuantileReal shape rate hs hr ⁻¹' Iic x) ∩ Ico 0 1 =
        Icc 0 (cdf (gammaMeasure shape rate) x) := by
      ext u
      constructor
      · intro h
        exact ⟨h.2.1, (gammaQuantileReal_le_iff hs hr h.2.1 h.2.2 hx).mp h.1⟩
      · intro h
        have hu1 := h.2.trans_lt (gamma_cdf_lt_one hs hr hx)
        exact ⟨(gammaQuantileReal_le_iff hs hr h.1 hu1 hx).mpr h.2, h.1, hu1⟩
    rw [he, Real.volume_Icc, sub_zero, ofReal_cdf]
  · have he : (gammaQuantileReal shape rate hs hr ⁻¹' Iic x) ∩ Ico 0 1 = ∅ := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false,
        not_and]
      intro h
      exact False.elim (hx ((gammaQuantileReal_nonneg hs hr u).trans h))
    have hc : cdf (gammaMeasure shape rate) x = 0 := by
      apply le_antisymm _ (cdf_nonneg _ _)
      have hh := monotone_cdf (gammaMeasure shape rate) (le_of_not_ge hx)
      simpa only [gamma_cdf_zero hs hr] using hh
    rw [he, measure_empty, ← ofReal_cdf, hc, ENNReal.ofReal_zero]

/-- The extended Gamma quantile used for upper rounding takes the value infinity at `u = 1`. -/
noncomputable def gammaQuantileExtended (shape rate : ℝ) (hs : 0 < shape) (hr : 0 < rate)
    (u : ℝ) : ℝ≥0∞ :=
  if u = 1 then ⊤ else ENNReal.ofReal (gammaQuantileReal shape rate hs hr u)

lemma gammaQuantileExtended_one {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    gammaQuantileExtended shape rate hs hr 1 = ⊤ := by
  simp [gammaQuantileExtended]

lemma gammaQuantileExtended_measurable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    Measurable (gammaQuantileExtended shape rate hs hr) := by
  exact Measurable.ite (measurableSet_singleton 1) measurable_const
    (gammaQuantileReal_measurable hs hr).ennreal_ofReal

/-- The extended quantile has the Gamma law embedded into `ℝ≥0∞`; its endpoint value affects no probability. -/
lemma gammaQuantileExtended_map {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    Measure.map (gammaQuantileExtended shape rate hs hr) unitUniform =
      Measure.map ENNReal.ofReal (gammaMeasure shape rate) := by
  let : NullSingletonClass unitUniform := by
    unfold unitUniform
    infer_instance
  have he : gammaQuantileExtended shape rate hs hr =ᵐ[unitUniform]
      (fun u => ENNReal.ofReal (gammaQuantileReal shape rate hs hr u)) := by
    filter_upwards [unitUniform.ae_ne 1] with u hu
    simp [gammaQuantileExtended, hu]
  rw [Measure.map_congr he]
  calc
    _ = Measure.map ENNReal.ofReal
        (Measure.map (gammaQuantileReal shape rate hs hr) unitUniform) := by
      exact (Measure.map_map (μ := unitUniform) (g := ENNReal.ofReal)
        (f := gammaQuantileReal shape rate hs hr) ENNReal.measurable_ofReal
        (gammaQuantileReal_measurable hs hr)).symm
    _ = _ := by rw [gammaQuantileReal_map hs hr]

end GammaFPP

end OAI
