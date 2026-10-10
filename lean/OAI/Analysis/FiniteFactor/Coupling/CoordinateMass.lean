import OAI.Analysis.FiniteFactor.Coupling.Infinite

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Endpoint tails of the original Haar representative have at most their
interval length; the endpoint singleton conventions cause no extra mass. -/
theorem unitIntervalMeasure_right_tail (a : ℝ) :
    unitIntervalMeasure (Set.Ici (1-a)) ≤ ENNReal.ofReal a := by
  rw [unitIntervalMeasure,Measure.restrict_apply measurableSet_Ici]
  have hs : Set.Ici (1-a) ∩ Set.Ico (0 : ℝ) 1 ⊆ Set.Icc (1-a) 1 :=
    fun _ h => ⟨h.1,h.2.2.le⟩
  exact (measure_mono hs).trans_eq (by simp [Real.volume_Icc])

theorem unitIntervalMeasure_left_tail (a : ℝ) :
    unitIntervalMeasure (Set.Iic a) ≤ ENNReal.ofReal a := by
  rw [unitIntervalMeasure,Measure.restrict_apply measurableSet_Iic]
  have hs : Set.Iic a ∩ Set.Ico (0 : ℝ) 1 ⊆ Set.Icc 0 a :=
    fun _ h => ⟨h.2.1,h.1⟩
  exact (measure_mono hs).trans_eq (by simp [Real.volume_Icc])

namespace CouplingParameters

theorem labelledCoupling_label (p : CouplingParameters) (l : Fin 6) :
    p.labelledCoupling {z | z.1 = l} = ENNReal.ofReal (p.labelMass l) := by
  have hm : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.1 = l} :=
    (measurableSet_singleton l).preimage measurable_fst
  have hi (i : Fin 6) : ((p.pairComponentLaw i).map (fun xy => (i,xy))) {z | z.1 = l} =
      if i = l then 1 else 0 := by
    have hmeas : Measurable (fun xy : ℝ × ℝ => (i,xy)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hmeas hm]
    by_cases h : i = l <;> simp [h]
  rw [labelledCoupling,Measure.finsetSum_apply]
  simp only [Measure.smul_apply,smul_eq_mul,hi]
  simp

/-- The actual one-coordinate endpoint law is dominated by ten times Haar. -/
theorem labelledEndpoint_set_le_ten (p : CouplingParameters) (b : Bool)
    (A : Set ℝ) (hA : MeasurableSet A) :
    p.labelledCoupling ((fun z => endpoint b z.2) ⁻¹' A) ≤ 10*unitIntervalMeasure A := by
  have hmeas : Measurable (fun z : Fin 6 × (ℝ × ℝ) => endpoint b z.2) :=
    (endpoint_measurable b).comp measurable_snd
  rw [← Measure.map_apply hmeas hA,labelled_endpoint_density]
  change (unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.endpointDensity b t))) A ≤ _
  rw [withDensity_apply _ hA]
  have hh := lintegral_mono (μ := unitIntervalMeasure.restrict A)
    (fun t => ENNReal.ofReal_le_ofReal ((p.endpointDensity_lt_ten b t).le))
  simpa only [ENNReal.ofReal_ofNat,lintegral_const,Measure.restrict_apply_univ] using hh

theorem labelledCoupling_right_tail (p : CouplingParameters) (a : ℝ) :
    p.labelledCoupling {z | 1-a ≤ z.2.1} ≤ ENNReal.ofReal (10*a) := by
  have hh := p.labelledEndpoint_set_le_ten false (Set.Ici (1-a)) measurableSet_Ici
  apply hh.trans
  exact (mul_le_mul le_rfl (unitIntervalMeasure_right_tail a) zero_le zero_le).trans_eq
    (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]; simp)

theorem labelledCoupling_left_tail (p : CouplingParameters) (a : ℝ) :
    p.labelledCoupling {z | z.2.2 ≤ a} ≤ ENNReal.ofReal (10*a) := by
  have hh := p.labelledEndpoint_set_le_ten true (Set.Iic a) measurableSet_Iic
  apply hh.trans
  exact (mul_le_mul le_rfl (unitIntervalMeasure_left_tail a) zero_le zero_le).trans_eq
    (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]; simp)

end CouplingParameters
end
end FiniteFactor

end OAI
