import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileParameterLaw

namespace OAI

open MeasureTheory Set Filter
open scoped Topology

namespace Balanced.ProfileDetection

theorem product_positiveDetection_mass_ae {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (V : Set A) (hV : MeasurableSet V) (h : A × ℝ → ℝ) (hh : Measurable h)
    (hparam : ∀ᵐ z : ℝ ∂τ, z ∈ Ioo 0 1)
    (hfibers : ∀ᵐ x ∂ν,
      (x ∈ V → ∀ᵐ z : ℝ ∂τ, h (x, z) ≠ 0) ∧
      (x ∉ V → ∀ᵐ z : ℝ ∂τ, h (x, z) = 0)) :
    (ν.prod τ) (positiveDetection Prod.snd h) = ν V := by
  have hD : MeasurableSet (positiveDetection Prod.snd h) := by
    unfold positiveDetection
    measurability
  have hM : MeasurableSet {p : A × ℝ |
      (p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V)} :=
    hD.iff (hV.preimage measurable_fst)
  have hAE : ∀ᵐ p : A × ℝ ∂ν.prod τ,
      p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V := by
    apply (Measure.ae_prod_iff_ae_ae hM).mpr
    filter_upwards [hfibers] with x hx
    by_cases hVx : x ∈ V
    · filter_upwards [hparam, hx.1 hVx] with z hz hn
      simp only [positiveDetection, mem_ofPred_eq, hVx, iff_true]
      exact ⟨hz.1, hz.2, hn⟩
    · filter_upwards [hx.2 hVx] with z hz
      simp [positiveDetection, hVx, hz]
  calc
    (ν.prod τ) (positiveDetection Prod.snd h) = (ν.prod τ) (V ×ˢ (univ : Set ℝ)) := by
      apply measure_congr
      filter_upwards [hAE] with p hp
      apply propext
      change (p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V ∧ p.2 ∈ (univ : Set ℝ))
      simpa only [mem_univ, and_true] using hp
    _ = ν V := by rw [Measure.prod_prod]; simp

end Balanced.ProfileDetection

namespace Balanced.ProfileDetectionLimit

open ProfileDetection ProfileDetectionBridge ProfileParameterLaw

theorem measurableSet_deletionVisible (P : Profile) : MeasurableSet (deletionVisible P) := by
  unfold deletionVisible deletionInvisible
  measurability

theorem measurableSet_coverVisible (P : Profile) : MeasurableSet (coverVisible P) := by
  unfold coverVisible coverInvisible
  measurability

noncomputable def dDiscrepancy (P : Profile) (p : Profile × ℝ) : ℝ :=
  dTest p.1 p.2 - planeTest P p.2

noncomputable def cDiscrepancy (P : Profile) (p : Profile × ℝ) : ℝ :=
  cTest p.1 p.2 - planeTest P p.2

theorem measurable_dDiscrepancy (P : Profile) : Measurable (dDiscrepancy P) :=
  measurable_dTest.sub (measurable_planeTest.comp (measurable_const.prodMk measurable_snd))

theorem measurable_cDiscrepancy (P : Profile) : Measurable (cDiscrepancy P) :=
  measurable_cTest.sub (measurable_planeTest.comp (measurable_const.prodMk measurable_snd))

theorem tendsto_dCutoff_visible_mass (ν : Measure Profile) (P : Profile)
    (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ j, x (0, j) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw 1))
      (cutoffDetection Prod.snd (dDiscrepancy P) n)) atTop
      (𝓝 (ν (deletionVisible P))) := by
  let : IsProbabilityMeasure (parameterLaw 1) := parameterLaw_isProbabilityMeasure (by norm_num)
  have hmass := product_positiveDetection_mass_ae ν (parameterLaw 1)
    (deletionVisible P) (measurableSet_deletionVisible P)
    (dDiscrepancy P) (measurable_dDiscrepancy P) (ae_parameterLaw_mem 1)
  have hdet : (ν.prod (parameterLaw 1)) (positiveDetection Prod.snd (dDiscrepancy P)) =
      ν (deletionVisible P) := by
    apply hmass
    filter_upwards [hν] with x hx
    constructor
    · intro hvisible
      have hne := ae_parameterLaw_of_ae 1 (d_visible_ae_ne x P hx.1 hP hx.2 hvisible)
      filter_upwards [hne] with z hz
      exact sub_ne_zero.mpr hz
    · intro hinvisible
      have hxP : deletionInvisible P x := by simpa [deletionVisible] using hinvisible
      exact Eventually.of_forall fun z => sub_eq_zero.mpr (d_invisible_eq x P hxP z)
  simpa only [hdet] using tendsto_measure_cutoffDetection (ν.prod (parameterLaw 1))
    Prod.snd (dDiscrepancy P)

theorem tendsto_cCutoff_visible_mass (ν : Measure Profile) (P : Profile)
    (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ i, x (i, 0) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw (Real.sqrt 2)))
      (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 (ν (coverVisible P))) := by
  let : IsProbabilityMeasure (parameterLaw (Real.sqrt 2)) :=
    parameterLaw_isProbabilityMeasure (Real.sqrt_pos.mpr (by norm_num))
  have hmass := product_positiveDetection_mass_ae ν (parameterLaw (Real.sqrt 2))
    (coverVisible P) (measurableSet_coverVisible P)
    (cDiscrepancy P) (measurable_cDiscrepancy P) (ae_parameterLaw_mem (Real.sqrt 2))
  have hdet : (ν.prod (parameterLaw (Real.sqrt 2))) (positiveDetection Prod.snd (cDiscrepancy P)) =
      ν (coverVisible P) := by
    apply hmass
    filter_upwards [hν] with x hx
    constructor
    · intro hvisible
      have hne := ae_parameterLaw_of_ae (Real.sqrt 2) (c_visible_ae_ne x P hx.1 hP hx.2 hvisible)
      filter_upwards [hne] with z hz
      exact sub_ne_zero.mpr hz
    · intro hinvisible
      have hxP : coverInvisible P x := by simpa [coverVisible] using hinvisible
      exact Eventually.of_forall fun z => sub_eq_zero.mpr (c_invisible_eq x P hxP z)
  simpa only [hdet] using tendsto_measure_cutoffDetection (ν.prod (parameterLaw (Real.sqrt 2)))
    Prod.snd (cDiscrepancy P)

theorem tendsto_dCutoff_visible_mass_real (ν : Measure Profile) [IsFiniteMeasure ν]
    (P : Profile) (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ j, x (0, j) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw 1)).real
      (cutoffDetection Prod.snd (dDiscrepancy P) n)) atTop
      (𝓝 (ν.real (deletionVisible P))) :=
  (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp
    (tendsto_dCutoff_visible_mass ν P hP hν)

theorem tendsto_cCutoff_visible_mass_real (ν : Measure Profile) [IsFiniteMeasure ν]
    (P : Profile) (hP : Summable P)
    (hν : ∀ᵐ x ∂ν, Summable x ∧ ∀ i, x (i, 0) = 0) :
    Tendsto (fun n : ℕ => (ν.prod (parameterLaw (Real.sqrt 2))).real
      (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 (ν.real (coverVisible P))) :=
  (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp
    (tendsto_cCutoff_visible_mass ν P hP hν)

theorem tendsto_cutoff_sum_visible_mass (νD νC : FiniteMeasure Profile)
    (P : Profile) (hP : Summable P)
    (hD : ∀ᵐ x ∂(νD : Measure Profile), Summable x ∧ ∀ j, x (0, j) = 0)
    (hC : ∀ᵐ x ∂(νC : Measure Profile), Summable x ∧ ∀ i, x (i, 0) = 0) :
    Tendsto (fun n : ℕ =>
      ((νD : Measure Profile).prod (parameterLaw 1)).real
        (cutoffDetection Prod.snd (dDiscrepancy P) n) +
      ((νC : Measure Profile).prod (parameterLaw (Real.sqrt 2))).real
        (cutoffDetection Prod.snd (cDiscrepancy P) n)) atTop
      (𝓝 ((νD : Measure Profile).real (deletionVisible P) +
        (νC : Measure Profile).real (coverVisible P))) :=
  (tendsto_dCutoff_visible_mass_real νD P hP hD).add
    (tendsto_cCutoff_visible_mass_real νC P hP hC)

end Balanced.ProfileDetectionLimit

end OAI
