import OAI.Probability.SLE.Mass.LevelApproximants
import OAI.Probability.SLE.Loewner.ActualRadiusStops

namespace OAI

/-! The conditional Green kernel of the part of a level measure still to
come. The level hit is represented by an actual Brownian stopping time;
no measurability of a geometrically defined filtration is assumed. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

def levelRemainderGreen {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u then
    stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u else 0

def levelCurrentGreen {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u then
    greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z else 0

lemma levelRemainderGreen_nonneg
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}
    {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (t : ℝ≥0) (z : ℂ) : 0 ≤ levelRemainderGreen κ B γ G u t z ω := by
  unfold levelRemainderGreen
  split_ifs
  · exact stoppedGreen_nonneg hw κ z u
  · exact le_rfl

lemma levelCurrentGreen_nonneg
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}
    {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (t : ℝ≥0) (z : ℂ) : 0 ≤ levelCurrentGreen κ B γ G u t z ω := by
  unfold levelCurrentGreen
  split_ifs
  · exact greenDensity_nonneg hw κ t z
  · exact le_rfl

lemma actual_greenDensity_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) : Measurable (fun q : Ω × ℂ =>
      greenDensity κ (fun s => Real.sqrt κ * B s q.1) (γ q.1) (G q.1) t q.2) := by
  let U (s : ℝ≥0) (ω : Ω) := Real.sqrt κ * B s ω
  let c := spatialClippedFamily U (hBm.const_mul _) (fun ω => (hBc ω).const_mul _)
  have hj := c.jointGreen_measurable κ B hBm
  have hp : Measurable (fun q : Ω × ℂ => (t, q.2, q.1)) :=
    measurable_const.prodMk (measurable_snd.prodMk measurable_fst)
  have hh := hj.comp hp
  have he (q : Ω × ℂ) : c.jointGreen κ B (t,q.2,q.1) =
      greenDensity κ (fun s => Real.sqrt κ * B s q.1) (γ q.1) (G q.1) t q.2 :=
    c.jointGreen_eq κ B q.1 ((hBc q.1).const_mul _) (fun _ => rfl) (hw q.1) t q.2
  simpa only [Function.comp_def, he] using hh

lemma levelRemainderGreen_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) : Measurable (fun q : Ω × ℂ => levelRemainderGreen κ B γ G u t q.2 q.1) := by
  exact Measurable.ite
    (measurableSet_lt measurable_const (actual_radiusLevel_joint_measurable hm hBc κ u hu γ G F hw))
    (actual_stoppedGreen_joint_measurable hm hBc κ u hu γ G F hw) measurable_const

lemma levelCurrentGreen_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) : Measurable (fun q : Ω × ℂ => levelCurrentGreen κ B γ G u t q.2 q.1) := by
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  exact Measurable.ite
    (measurableSet_lt measurable_const (actual_radiusLevel_joint_measurable hm hBc κ u hu γ G F hw))
    (actual_greenDensity_joint_measurable hBm hBc κ γ G F hw t) measurable_const

theorem levelRemainderGreen_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) :
    let hm (s : ℝ≥0) : Measurable (B s) :=
      hBm.comp (measurable_const.prodMk measurable_id)
    let ℱ := Filtration.natural B (fun s => (hm s).stronglyMeasurable)
    Integrable (levelRemainderGreen κ B γ G u t z) P ∧
      Integrable (levelCurrentGreen κ B γ G u t z) P ∧
      P[levelRemainderGreen κ B γ G u t z | ℱ t] =ᵐ[P]
        levelCurrentGreen κ B γ G u t z := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let hm (s : ℝ≥0) : Measurable (B s) :=
    hBm.comp (measurable_const.prodMk measurable_id)
  let ℱ := Filtration.natural B (fun s => (hm s).stronglyMeasurable)
  obtain ⟨M, Z, _, hZ, _, _, hClosed, _, heq, _⟩ :=
    exists_physical_green_stopping_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz u hu
  obtain ⟨τ, hτ, _, hτeq⟩ := exists_monotone_radiusLevel_stops hB hm hBm hBc hB0
    κ hκ hκ8 γ G F hw z hz (fun _ => u) (fun _ => hu) (fun _ _ _ => le_rfl)
  let A : Set Ω := {ω | ¬ τ 0 ω ≤ (t : WithTop ℝ≥0)}
  have hA : MeasurableSet[ℱ t] A := (hτ 0 t).compl
  have hAg : MeasurableSet A := ℱ.le t _ hA
  have hR : levelRemainderGreen κ B γ G u t z =ᵐ[P] A.indicator Z := by
    filter_upwards [heq, hτeq] with ω he hte
    have htest : (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u ↔ ω ∈ A := by
      change (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u ↔ ¬ τ 0 ω ≤ (t : ℝ≥0∞)
      rw [hte 0]
      exact lt_iff_not_ge
    by_cases ha : ω ∈ A
    · rw [levelRemainderGreen, ite_eq_left (htest.mpr ha), indicator_of_mem ha, he.2]
    · rw [levelRemainderGreen, ite_eq_right (mt htest.mp ha), indicator_of_notMem ha]
  have hC : levelCurrentGreen κ B γ G u t z =ᵐ[P] A.indicator (M t) := by
    filter_upwards [heq, hτeq] with ω he hte
    have htest : (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u ↔ ω ∈ A := by
      change (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u ↔ ¬ τ 0 ω ≤ (t : ℝ≥0∞)
      rw [hte 0]
      exact lt_iff_not_ge
    by_cases ha : ω ∈ A
    · rw [levelCurrentGreen, ite_eq_left (htest.mpr ha), indicator_of_mem ha,
        he.1 t, physicalStoppedGreen, ite_eq_right (not_le.mpr (htest.mpr ha))]
    · rw [levelCurrentGreen, ite_eq_right (mt htest.mp ha), indicator_of_notMem ha]
  refine ⟨(hZ.indicator hAg).congr hR.symm,
    ((integrable_condExp.congr (hClosed t).symm).indicator hAg).congr hC.symm, ?_⟩
  apply (condExp_congr_ae hR).trans
  apply (condExp_indicator hZ hA).trans
  apply EventuallyEq.trans _ hC.symm
  filter_upwards [hClosed t] with ω he
  by_cases ha : ω ∈ A
  · simpa only [indicator_of_mem ha,ℱ,hm] using he.symm
  · simp only [indicator_of_notMem ha]

theorem levelRemainderGreen_setIntegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0)
    (A : Set Ω)
    (hA : MeasurableSet[Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable) t] A) :
    (∫ ω in A, levelRemainderGreen κ B γ G u t z ω ∂P) =
      ∫ ω in A, levelCurrentGreen κ B γ G u t z ω ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  obtain ⟨hR, _, he⟩ := levelRemainderGreen_condExp hB hBm hBc hB0 hκ hκ8
    γ G F hw z hz u hu t
  have : IsFiniteMeasure (P.trim (ℱ.le t)) := isFiniteMeasure_trim (ℱ.le t)
  exact (setIntegral_condExp (ℱ.le t) hR hA).symm.trans
    (integral_congr_ae (ae_restrict_of_ae he))

theorem levelRemainderGreen_setLIntegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0)
    (A : Set Ω)
    (hA : MeasurableSet[Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable) t] A) :
    (∫⁻ ω in A, ENNReal.ofReal (levelRemainderGreen κ B γ G u t z ω) ∂P) =
      ∫⁻ ω in A, ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω) ∂P := by
  obtain ⟨hR,hC,_⟩ := levelRemainderGreen_condExp hB hBm hBc hB0 hκ hκ8 γ G F hw z hz u hu t
  have hRn : ∀ᵐ ω ∂P.restrict A, 0 ≤ levelRemainderGreen κ B γ G u t z ω :=
    ae_restrict_of_ae (hw.mono (fun ω hω => levelRemainderGreen_nonneg ω hω u t z))
  have hCn : ∀ᵐ ω ∂P.restrict A, 0 ≤ levelCurrentGreen κ B γ G u t z ω :=
    ae_restrict_of_ae (hw.mono (fun ω hω => levelCurrentGreen_nonneg ω hω u t z))
  rw [← ofReal_integral_eq_lintegral_ofReal hR.integrableOn hRn,
    ← ofReal_integral_eq_lintegral_ofReal hC.integrableOn hCn]
  rw [levelRemainderGreen_setIntegral hB hBm hBc hB0 hκ hκ8 γ G F hw z hz u hu t A hA]

/-- The finite-level kernel identity against every nonnegative spatial
test, on every event known at time `t`. -/
theorem levelRemainderGreen_spatial_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) (K : Set ℂ)
    (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (A : Set Ω)
    (hA : MeasurableSet[Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable) t] A) :
    (∫⁻ ω in A, (∫⁻ z in K, f z * ENNReal.ofReal (levelRemainderGreen κ B γ G u t z ω) ∂volume) ∂P) =
      ∫⁻ ω in A, (∫⁻ z in K, f z * ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω) ∂volume) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hmR := levelRemainderGreen_joint_measurable hm hBc κ u hu γ G F hw t
  have hmC := levelCurrentGreen_joint_measurable hBm hBc κ u hu γ G F hw t
  have hR := (hf.comp measurable_snd).mul hmR.ennreal_ofReal
  have hC := (hf.comp measurable_snd).mul hmC.ennreal_ofReal
  conv_lhs => rw [lintegral_lintegral_swap hR.aemeasurable]
  conv_rhs => rw [lintegral_lintegral_swap hC.aemeasurable]
  apply setLIntegral_congr_fun hK
  intro z hz
  dsimp only
  have hpz : Measurable (fun ω : Ω => (ω,z)) := measurable_id.prodMk measurable_const
  have hmRz : Measurable (fun ω => ENNReal.ofReal (levelRemainderGreen κ B γ G u t z ω)) :=
    by
      have hh := hmR.ennreal_ofReal.comp hpz
      simpa only [Function.comp_def] using hh
  have hmCz : Measurable (fun ω => ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω)) :=
    by
      have hh := hmC.ennreal_ofReal.comp hpz
      simpa only [Function.comp_def] using hh
  rw [lintegral_const_mul _ hmRz, lintegral_const_mul _ hmCz]
  rw [levelRemainderGreen_setLIntegral hB hBm hBc hB0 hκ hκ8 γ G F (ae_of_all _ hw)
    z (hKH hz) u hu t A hA]

end SLEExactGauge.Multipoint

end

end OAI
