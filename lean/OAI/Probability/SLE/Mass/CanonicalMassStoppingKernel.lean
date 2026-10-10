import OAI.Probability.SLE.Mass.CanonicalMassRandomTime
import OAI.Probability.SLE.Stochastic.ProgressiveRandomTime

namespace OAI

/-! The canonical mass has the exact conditional Green kernel at every
possibly infinite stopping time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma extendedCanonicalMass_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (N : ℝ≥0 → Ω → Measure upperHalfPlane) (ν : Ω → Measure upperHalfPlane)
    (hN : IsProgressive ℱ N) (hν : Measurable ν)
    (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun ω => extendedCanonicalMass N ν (S ω) ω) :=
  Measurable.ite (measurableSet_lt hS measurable_const)
    (_root_.OAI.MeasureTheory.IsProgressive.extended_random_time_measurable hN S hS) hν

theorem RationalCanonicalMass.stopping_conditional_kernel
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (C : RationalCanonicalMass P κ B hBm γ G)
    (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (hNp : IsProgressive (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) N)
    (hNr : ∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω))
    (hpath : ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => C.mass q ω)
      (C.terminal ω) (fun t => N t ω))
    (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S)
    (E : Set Ω) (hE : MeasurableSet[hS.measurableSpace] E) :
    (P.restrict E).bind C.terminal =
      (P.restrict E).bind (fun ω => extendedCanonicalMass N C.terminal (S ω) ω) +
      (P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S) := by
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let V (ω : Ω) := extendedCanonicalMass N C.terminal (S ω) ω
  have hVm : Measurable V := extendedCanonicalMass_measurable _ N C.terminal hNp
    C.terminal_measurable S hS.measurable'
  have hVr (ω : Ω) := extendedCanonicalMass_radon N C.terminal hNr C.terminal_radon (S ω) ω
  have hVdom : ∀ᵐ ω ∂P, V ω ≤ C.terminal ω := by
    filter_upwards [hpath] with ω hω
    dsimp only [V,extendedCanonicalMass]
    split_ifs
    · exact hω.dominated _
    · exact le_rfl
  have hVmean := restricted_bind_le_of_ae_le P V C.terminal hVm C.terminal_measurable hVdom E
  rw [C.mean] at hVmean
  have hTmean := restricted_bind_le_of_ae_le P C.terminal C.terminal
    C.terminal_measurable C.terminal_measurable (ae_of_all _ (fun _ => le_rfl)) E
  rw [C.mean] at hTmean
  have hGmean := halfPlaneStoppingGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw S hS E
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind V) :=
    ⟨fun K hK => lt_of_le_of_lt (hVmean K) hK.measure_lt_top⟩
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind C.terminal) :=
    ⟨fun K hK => lt_of_le_of_lt (hTmean K) hK.measure_lt_top⟩
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S)) :=
    ⟨fun K hK => lt_of_le_of_lt (hGmean K) hK.measure_lt_top⟩
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind V +
      (P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S)) := by
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩
  let M (n : ℕ) (t : ℝ≥0∞) := convexLevelMeasure κ B γ G (fun n => (n:ℝ))
    C.supports C.weights n t
  have hMm (n : ℕ) (T : Ω → ℝ≥0∞) (hT : Measurable T) :=
    convexLevelMeasure_random_time_measurable hm hBc κ γ G F hw (fun n => (n:ℝ))
      (fun n => Nat.cast_nonneg n) C.supports C.weights n T hT
  have hMmean (n : ℕ) (T : Ω → ℝ≥0∞) (hT : Measurable T) :
      (P.restrict E).bind (fun ω => M n (T ω) ω) ≤ initialGreenMeasure κ := by
    have hh := restricted_bind_le_of_ae_le P _ _ (hMm n T hT)
      (convexLevelMeasure_measurable hm hBc κ γ G F hw _ (fun n => Nat.cast_nonneg n)
        C.supports C.weights n ∞)
      (ae_of_all _ (fun ω => convexLevelMeasure_mono κ B γ G (fun n => (n:ℝ))
        C.supports C.weights n ω le_top)) E
    rwa [convexLevelMeasure_terminal_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw _
      (fun n => Nat.cast_nonneg n) C.supports C.weights C.weights_nonneg C.weights_sum] at hh
  let (ω : Ω) : IsFiniteMeasureOnCompacts (V ω) := (hVr ω).2
  let (ω : Ω) : IsFiniteMeasureOnCompacts (C.terminal ω) := (C.terminal_radon ω).2
  let (n : ℕ) (t : ℝ≥0∞) (ω : Ω) : IsFiniteMeasureOnCompacts (M n t ω) :=
    convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) _ C.supports C.weights n t
  apply (localTestFamily upperHalfPlane).measure_eq_of_test_integrals
  intro k
  let f := (localTestFamily upperHalfPlane).test k
  have heM (n : ℕ) (T : Ω → ℝ≥0∞) (hT : Measurable T) :
      (∫ ω in E, (∫ z, f z ∂M n (T ω) ω) ∂P) =
      ∫ z, f z ∂(P.restrict E).bind (fun ω => M n (T ω) ω) :=
    integral_bind_of_integrable_sections (P.restrict E) _ (hMm n T hT)
      f f.continuous.measurable (fun _ => f.integrable) (f.integrable.mono_measure (hMmean n T hT))
  have heV : (∫ ω in E, (∫ z, f z ∂V ω) ∂P) = ∫ z, f z ∂(P.restrict E).bind V :=
    integral_bind_of_integrable_sections (P.restrict E) V hVm f f.continuous.measurable
      (fun _ => f.integrable) f.integrable
  have heT : (∫ ω in E, (∫ z, f z ∂C.terminal ω) ∂P) = ∫ z, f z ∂(P.restrict E).bind C.terminal :=
    integral_bind_of_integrable_sections (P.restrict E) C.terminal C.terminal_measurable
      f f.continuous.measurable (fun _ => f.integrable) f.integrable
  have ht := (C.random_time_test_mean_tendsto hB hBm hBc hB0 hκ hκ8 F hw hgrowth N hNr hpath
    (fun _ => ∞) measurable_const E f).2
  simp only [extendedCanonicalMass,lt_self_iff_false,ite_false,heT] at ht
  change Tendsto (fun n => ∫ ω in E, (∫ z, f z ∂M n ∞ ω) ∂P) atTop
    (𝓝 (∫ z, f z ∂(P.restrict E).bind C.terminal)) at ht
  have heInfinity (n : ℕ) := heM n (fun _ => ∞) measurable_const
  simp only [heInfinity] at ht
  have hv := (C.random_time_test_mean_tendsto hB hBm hBc hB0 hκ hκ8 F hw hgrowth N hNr hpath
    S hS.measurable' E f).2
  change Tendsto (fun n => ∫ ω in E, (∫ z, f z ∂M n (S ω) ω) ∂P) atTop
    (𝓝 (∫ ω in E, (∫ z, f z ∂V ω) ∂P)) at hv
  have heS (n : ℕ) := heM n S hS.measurable'
  simp only [heV,heS] at hv
  have hg := convexStoppingCurrentMean_test_tendsto hB hBm hBc hB0 hκ hκ8 γ G F hw
    (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg n) (fun _ _ h => Nat.cast_le.mpr h)
    tendsto_natCast_atTop_atTop C.supports C.weights C.weights_nonneg C.weights_sum S hS E f
  have he (n : ℕ) : (∫ z, f z ∂(P.restrict E).bind (M n ∞)) =
      (∫ z, f z ∂(P.restrict E).bind (fun ω => M n (S ω) ω)) +
      ∫ z, f z ∂convexStoppingCurrentMean (P.restrict E) κ B γ G
        (fun n => (n:ℝ)) C.supports C.weights n S := by
    rw [convexLevelMeasure_stopping_conditional_split hB hBm hBc hB0 hκ hκ8 γ G F hw
      _ (fun n => Nat.cast_nonneg n) C.supports C.weights n S hS E hE]
    exact integral_add_measure (f.integrable.mono_measure (hMmean n S hS.measurable'))
      (f.integrable.mono_measure (convexStoppingCurrentMean_le hB hBm hBc hB0 hκ hκ8 γ G F hw
        _ (fun n => Nat.cast_nonneg n) C.supports C.weights C.weights_nonneg C.weights_sum n S hS E))
  rw [integral_add_measure f.integrable f.integrable]
  exact tendsto_nhds_unique ht ((hv.add hg).congr' (Eventually.of_forall (fun n => (he n).symm)))

end SLEExactGauge.Multipoint

end

end OAI
