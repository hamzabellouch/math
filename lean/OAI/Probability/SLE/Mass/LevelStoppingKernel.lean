import OAI.Probability.SLE.Mass.LevelApproximationKernel
import OAI.Probability.SLE.Loewner.ActualRadiusStopsRegular
import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! The finite-level remaining Green kernel at any Brownian stopping
time. Both sides vanish at an infinite stopping time. Finite cutoffs use
the existing optional identity for the stopped Green martingale. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

def levelStoppingRemainderGreen {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (S : Ω → ℝ≥0∞) (z : ℂ) (ω : Ω) : ℝ :=
  if S ω < radiusLevelTime (γ ω) (G ω) z u then
    stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u else 0

def levelStoppingCurrentGreen {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (S : Ω → ℝ≥0∞) (z : ℂ) (ω : Ω) : ℝ :=
  if S ω < radiusLevelTime (γ ω) (G ω) z u then
    greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (S ω).toNNReal z else 0

lemma levelStoppingRemainderGreen_nonneg
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (S : Ω → ℝ≥0∞) (z : ℂ) (ω : Ω) :
    0 ≤ levelStoppingRemainderGreen κ B γ G u S z ω := by
  unfold levelStoppingRemainderGreen
  split_ifs
  · exact stoppedGreen_nonneg (hw ω) κ z u
  · exact le_rfl

lemma levelStoppingCurrentGreen_nonneg
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (S : Ω → ℝ≥0∞) (z : ℂ) (ω : Ω) :
    0 ≤ levelStoppingCurrentGreen κ B γ G u S z ω := by
  unfold levelStoppingCurrentGreen
  split_ifs
  · exact greenDensity_nonneg (hw ω) κ _ z
  · exact le_rfl

theorem levelStoppingRemainderGreen_finite_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (levelStoppingRemainderGreen κ B γ G u (fun ω => σ ω) z) P ∧
      Integrable (levelStoppingCurrentGreen κ B γ G u (fun ω => σ ω) z) P ∧
      P[levelStoppingRemainderGreen κ B γ G u (fun ω => σ ω) z | hσ.measurableSpace] =ᵐ[P]
        levelStoppingCurrentGreen κ B γ G u (fun ω => σ ω) z := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨M,Z,_,hZi,_,_,_,hStop,heq,_⟩ := exists_physical_green_stopping_regular
    hB hBm hc hB0 κ hκ hκ8 γ G F (ae_of_all _ hw) z hz u hu
  have hτ := actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u hu
  let A : Set Ω := {ω | (σ ω : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u}
  have hA : MeasurableSet[hσ.measurableSpace] A := by
    have he : A = {ω | radiusLevelTime (γ ω) (G ω) z u ≤ (σ ω : WithTop ℝ≥0)}ᶜ := by
      ext ω
      change (σ ω : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u ↔
        ¬ radiusLevelTime (γ ω) (G ω) z u ≤ (σ ω : ℝ≥0∞)
      exact lt_iff_not_ge
    rw [he]
    exact (hτ.measurableSet_stopping_time_le hσ).compl
  have hAg : MeasurableSet A := hσ.measurableSpace_le _ hA
  have hR : levelStoppingRemainderGreen κ B γ G u (fun ω => σ ω) z =ᵐ[P] A.indicator Z := by
    filter_upwards [heq] with ω he
    by_cases ha : ω ∈ A
    · have ht : (σ ω : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u := ha
      rw [levelStoppingRemainderGreen,ite_eq_left ht,indicator_of_mem ha,he.2]
    · have ht : ¬ (σ ω : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u := ha
      rw [levelStoppingRemainderGreen,ite_eq_right ht,indicator_of_notMem ha]
  have hC : levelStoppingCurrentGreen κ B γ G u (fun ω => σ ω) z =ᵐ[P]
      A.indicator (fun ω => M (σ ω) ω) := by
    filter_upwards [heq] with ω he
    by_cases ha : ω ∈ A
    · have ht : (σ ω : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u := ha
      rw [levelStoppingCurrentGreen,ite_eq_left ht,indicator_of_mem ha,ENNReal.toNNReal_coe,
        he.1 (σ ω),physicalStoppedGreen,ite_eq_right (not_le.mpr ht)]
    · have ht : ¬ (σ ω : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u := ha
      rw [levelStoppingCurrentGreen,ite_eq_right ht,indicator_of_notMem ha]
  have hMi : Integrable (fun ω => M (σ ω) ω) P :=
    integrable_condExp.congr (hStop σ hσ).symm
  refine ⟨(hZi.indicator hAg).congr hR.symm,(hMi.indicator hAg).congr hC.symm,?_⟩
  apply (condExp_congr_ae hR).trans
  apply (condExp_indicator hZi hA).trans
  apply EventuallyEq.trans _ hC.symm
  filter_upwards [hStop σ hσ] with ω he
  by_cases ha : ω ∈ A
  · simpa only [indicator_of_mem ha] using he.symm
  · simp only [indicator_of_notMem ha]

theorem levelStoppingRemainderGreen_finite_setLIntegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A) :
    (∫⁻ ω in A, ENNReal.ofReal (levelStoppingRemainderGreen κ B γ G u (fun ω => σ ω) z ω) ∂P) =
      ∫⁻ ω in A, ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G u (fun ω => σ ω) z ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hR,hC,he⟩ := levelStoppingRemainderGreen_finite_condExp hB hBm hc hB0 hκ hκ8
    γ G F hw z hz u hu σ hσ
  have hRn : ∀ᵐ ω ∂P.restrict A, 0 ≤ levelStoppingRemainderGreen κ B γ G u (fun ω => σ ω) z ω :=
    ae_of_all _ (levelStoppingRemainderGreen_nonneg κ B γ G F hw u _ z)
  have hCn : ∀ᵐ ω ∂P.restrict A, 0 ≤ levelStoppingCurrentGreen κ B γ G u (fun ω => σ ω) z ω :=
    ae_of_all _ (levelStoppingCurrentGreen_nonneg κ B γ G F hw u _ z)
  rw [← ofReal_integral_eq_lintegral_ofReal hR.integrableOn hRn,
    ← ofReal_integral_eq_lintegral_ofReal hC.integrableOn hCn]
  congr 1
  have : IsFiniteMeasure (P.trim hσ.measurableSpace_le) := isFiniteMeasure_trim hσ.measurableSpace_le
  exact (setIntegral_condExp hσ.measurableSpace_le hR hA).symm.trans
    (integral_congr_ae (ae_restrict_of_ae he))

private lemma stopped_setLIntegral_cutoffs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Ω → ℝ≥0∞) (hS : Measurable S) (E : Set Ω) (f : Ω → ℝ≥0∞)
    (hz : ∀ ω, S ω = ∞ → f ω = 0) :
    (∫⁻ ω in E, f ω ∂P) =
      ⨆ n : ℕ, ∫⁻ ω in E ∩ {ω | S ω ≤ (n:ℝ≥0)}, f ω ∂P := by
  let A (n : ℕ) := E ∩ {ω | S ω ≤ (n:ℝ≥0)}
  have hmono : Monotone A := by
    intro n k hnk ω hω
    refine ⟨hω.1,?_⟩
    change S ω ≤ ((k:ℝ≥0):ℝ≥0∞)
    exact hω.2.trans (ENNReal.coe_le_coe.mpr (by exact_mod_cast hnk))
  have hcover : (⋃ n, A n) = E ∩ {ω | S ω < ∞} := by
    ext ω
    simp only [mem_iUnion,A,mem_inter_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨n,hnE,hn⟩
      exact ⟨hnE,hn.trans_lt ENNReal.coe_lt_top⟩
    · rintro ⟨hE,hfin⟩
      obtain ⟨n,hn⟩ := exists_nat_ge ((S ω).toReal)
      refine ⟨n,hE,?_⟩
      exact (ENNReal.toReal_le_toReal hfin.ne ENNReal.coe_ne_top).mp (by simpa using hn)
  have hsupp : f.support ⊆ {ω | S ω < ∞} := by
    intro ω hω
    by_contra hn
    exact hω (hz ω (top_le_iff.mp (le_of_not_gt hn)))
  calc
    (∫⁻ ω in E, f ω ∂P) = ∫⁻ ω in {ω | S ω < ∞}, f ω ∂P.restrict E :=
      (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ ω in E ∩ {ω | S ω < ∞}, f ω ∂P := by
      rw [Measure.restrict_restrict (measurableSet_lt hS measurable_const),inter_comm]
    _ = ∫⁻ ω in ⋃ n, A n, f ω ∂P := by rw [hcover]
    _ = _ := setLIntegral_iUnion_of_directed f hmono.directed_le

theorem levelStoppingRemainderGreen_setLIntegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S)
    (E : Set Ω) (hE : MeasurableSet[hS.measurableSpace] E) :
    (∫⁻ ω in E, ENNReal.ofReal (levelStoppingRemainderGreen κ B γ G u S z ω) ∂P) =
      ∫⁻ ω in E, ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G u S z ω) ∂P := by
  classical
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  have hRzero (ω : Ω) (hω : S ω = ∞) :
      ENNReal.ofReal (levelStoppingRemainderGreen κ B γ G u S z ω) = 0 := by
    simp [levelStoppingRemainderGreen,hω]
  have hCzero (ω : Ω) (hω : S ω = ∞) :
      ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G u S z ω) = 0 := by
    simp [levelStoppingCurrentGreen,hω]
  rw [stopped_setLIntegral_cutoffs P S hS.measurable' E _ hRzero,
    stopped_setLIntegral_cutoffs P S hS.measurable' E _ hCzero]
  apply iSup_congr
  intro n
  let σ := cutoffStop S (n:ℝ≥0)
  have hσ := cutoffStop_stopping ℱ S hS (n:ℝ≥0)
  have hlocal := levelStoppingRemainderGreen_finite_setLIntegral hB hBm hc hB0 hκ hκ8
    γ G F hw z hz u hu σ hσ (E ∩ {ω | S ω ≤ (n:ℝ≥0)})
    (cutoffStop_success_measurable ℱ S hS (n:ℝ≥0) E hE)
  have he (ω : Ω) (hω : ω ∈ E ∩ {ω | S ω ≤ (n:ℝ≥0)}) : (σ ω : ℝ≥0∞) = S ω := by
    change (cutoffStop S (n:ℝ≥0) ω : WithTop ℝ≥0) = S ω
    rw [cutoffStop_coe,min_eq_left hω.2]
  calc
    _ = ∫⁻ ω in E ∩ {ω | S ω ≤ (n:ℝ≥0)},
        ENNReal.ofReal (levelStoppingRemainderGreen κ B γ G u (fun ω => σ ω) z ω) ∂P := by
      apply setLIntegral_congr_fun (hS.measurableSpace_le _
        (hE.inter (hS.measurableSet_le' (n:ℝ≥0))))
      intro ω hω
      simp only [levelStoppingRemainderGreen,he ω hω]
      split_ifs <;> rfl
    _ = _ := hlocal
    _ = _ := by
      apply setLIntegral_congr_fun (hS.measurableSpace_le _
        (hE.inter (hS.measurableSet_le' (n:ℝ≥0))))
      intro ω hω
      simp only [levelStoppingCurrentGreen,he ω hω]
      split_ifs <;> rfl

end SLEExactGauge.Multipoint

end

end OAI
