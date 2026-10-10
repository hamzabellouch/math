import OAI.NumberTheory.JointDickman.Arithmetic.PrimeLogMeasure

namespace OAI

/-! # Support and mass of the logarithmic prime measures -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem primeLogMeasure_support (c : ℝ) {x : ℝ} (hx : 1 < x) :
    primeLogMeasure c x (Set.Ioc c 1)ᶜ = 0 := by
  apply NNReal.coe_injective
  rw [primeLogMeasure_apply, NNReal.coe_zero]
  apply sum_eq_zero
  intro p hp
  obtain ⟨hpm,hpc⟩ := mem_filter.mp hp
  obtain ⟨hpN,hp⟩ := Nat.mem_primesLE.mp hpm
  have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp hpN
  have hloc := (logPrimeLocation_mem_Ioc hx hp.pos c 1).mpr
    (show x^c < p ∧ (p : ℝ) ≤ x^1 by simpa using And.intro hpc hpx)
  exact ite_eq_right (by simpa only [Set.mem_compl_iff, not_not] using hloc)

theorem finiteMeasure_inter_of_support (μ : FiniteMeasure ℝ) {s : Set ℝ}
    (hμ : μ sᶜ = 0) {t : Set ℝ} (ht : MeasurableSet t) : μ (t ∩ s) = μ t := by
  have hnull : (μ : Measure ℝ) sᶜ = 0 := (μ.null_iff_toMeasure_null _).mp hμ
  have hr : (μ : Measure ℝ).restrict s = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    convert hnull using 1
  apply (ENNReal.coe_inj).mp
  simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [← Measure.restrict_apply ht, hr]

theorem finiteMeasure_Ioc_clip (μ : FiniteMeasure ℝ) {c : ℝ}
    (hμ : μ (Set.Ioc c 1)ᶜ = 0) (a b : ℝ) :
    μ (Set.Ioc a b) = μ (Set.Ioc (max a c) (min b 1)) := by
  rw [← Set.Ioc_inter_Ioc]
  exact (finiteMeasure_inter_of_support μ hμ measurableSet_Ioc).symm

theorem primeLogMeasure_mass (c x : ℝ) :
    ((primeLogMeasure c x).mass : ℝ) = ∑ p ∈ largePrimeSet x (x^c), 1/(p : ℝ) := by
  rw [FiniteMeasure.mass, primeLogMeasure_apply]
  simp

theorem logarithmicPrimeMeasure_support {c : ℝ} (hc : 0 < c) :
    logarithmicPrimeMeasure c (Set.Ioc c 1)ᶜ = 0 := by
  rw [logarithmicPrimeMeasure,
    FiniteMeasure.map_apply _ Real.measurable_exp measurableSet_Ioc.compl,
    logIntervalVolume, FiniteMeasure.mk_apply,
    Measure.restrict_apply (Real.measurable_exp measurableSet_Ioc.compl)]
  have he : (Real.exp ⁻¹' (Set.Ioc c 1)ᶜ) ∩ Set.Ioc (Real.log c) 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨ht,htc,ht0⟩
    apply ht
    change c < Real.exp t ∧ Real.exp t ≤ 1
    exact ⟨(Real.log_lt_iff_lt_exp hc).mp htc, by simpa using Real.exp_le_exp.mpr ht0⟩
  rw [he]
  simp

theorem logarithmicPrimeMeasure_mass {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ((logarithmicPrimeMeasure c).mass : ℝ) = -Real.log c := by
  have he := finiteMeasure_inter_of_support (logarithmicPrimeMeasure c)
    (logarithmicPrimeMeasure_support hc) MeasurableSet.univ
  simp only [Set.univ_inter] at he
  rw [FiniteMeasure.mass, ← he,
    logarithmicPrimeMeasure_Ioc hc le_rfl hc1 le_rfl, Real.log_one, zero_sub]

theorem primeLogMeasure_mass_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun x => ((primeLogMeasure c x).mass : ℝ)) atTop
      (𝓝 ((logarithmicPrimeMeasure c).mass : ℝ)) := by
  rw [logarithmicPrimeMeasure_mass hc hc1]
  apply (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (primeLogMeasure_mass c x).symm

theorem primeLogMeasure_all_intervals_tendsto {c : ℝ} (hc : 0 < c)
    (a b : ℝ) :
    Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ)) atTop
      (𝓝 ((logarithmicPrimeMeasure c) (Set.Ioc a b) : ℝ)) := by
  have he : (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ)) =ᶠ[atTop]
      (fun x => ((primeLogMeasure c x) (Set.Ioc (max a c) (min b 1)) : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact congrArg ((↑) : ℝ≥0 → ℝ)
      (finiteMeasure_Ioc_clip _ (primeLogMeasure_support c hx) a b)
  rw [finiteMeasure_Ioc_clip _ (logarithmicPrimeMeasure_support hc) a b]
  by_cases hab : max a c ≤ min b 1
  · rw [logarithmicPrimeMeasure_Ioc hc (le_max_right _ _) hab (min_le_right _ _)]
    exact (primeLogMeasure_interval_tendsto (hc.trans_le (le_max_right _ _))
      (le_max_right _ _) hab (min_le_right _ _)).congr' he.symm
  · have hempty : Set.Ioc (max a c) (min b 1) = ∅ := Set.Ioc_eq_empty_of_le (le_of_not_ge hab)
    have ht : Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc (max a c) (min b 1)) : ℝ))
        atTop (𝓝 ((logarithmicPrimeMeasure c) (Set.Ioc (max a c) (min b 1)) : ℝ)) := by
      simp only [hempty, FiniteMeasure.coeFn_def, measure_empty, ENNReal.toNNReal_zero, NNReal.coe_zero]
      exact tendsto_const_nhds
    exact ht.congr' he.symm

end JointDickman

end OAI
