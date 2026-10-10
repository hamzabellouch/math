import OAI.Probability.SLE.Mass.CanonicalMassAllTimes
import OAI.Probability.SLE.Mass.LevelStoppingConvex
import OAI.Probability.SLE.Mass.NonnegativeL2Passage

namespace OAI

/-! Evaluating the common convex sequence at any measurable extended time
preserves convergence in mean on every event. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def extendedCanonicalMass {Ω : Type*} (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (ν : Ω → Measure upperHalfPlane) (t : ℝ≥0∞) (ω : Ω) : Measure upperHalfPlane :=
  if t < ∞ then N t.toNNReal ω else ν ω

lemma extendedCanonicalMass_radon
    {Ω : Type*} (N : ℝ≥0 → Ω → Measure upperHalfPlane) (ν : Ω → Measure upperHalfPlane)
    (hN : ∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω))
    (hν : ∀ ω, (ν ω).Regular ∧ IsFiniteMeasureOnCompacts (ν ω)) (t : ℝ≥0∞) (ω : Ω) :
    (extendedCanonicalMass N ν t ω).Regular ∧
      IsFiniteMeasureOnCompacts (extendedCanonicalMass N ν t ω) := by
  unfold extendedCanonicalMass
  split_ifs
  · exact hN _ _
  · exact hν _

theorem RationalCanonicalMass.all_extended_times_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (C : RationalCanonicalMass P κ B hBm γ G)
    (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (hNr : ∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω))
    (hpath : ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => C.mass q ω)
      (C.terminal ω) (fun t => N t ω)) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0∞) (f : C_c(upperHalfPlane,ℝ)),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
        C.supports C.weights n t ω) atTop
        (𝓝 (∫ z, f z ∂extendedCanonicalMass N C.terminal t ω)) := by
  filter_upwards [C.all_finite_times_limit hBc hκ hκ8 F hw N hNr hpath,C.terminal_limit]
    with ω hf ht
  intro t f
  by_cases h : t < ∞
  · simpa only [extendedCanonicalMass,ite_eq_left h,ENNReal.coe_toNNReal h.ne] using hf t.toNNReal f
  · have he : t = ∞ := top_le_iff.mp (le_of_not_gt h)
    simpa only [he,extendedCanonicalMass,lt_self_iff_false,ite_false] using ht f

theorem RationalCanonicalMass.random_time_nonnegative_mean_tendsto
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
    (hNr : ∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω))
    (hpath : ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => C.mass q ω)
      (C.terminal ω) (fun t => N t ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) (E : Set Ω)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    Integrable (fun ω => ∫ z, f z ∂extendedCanonicalMass N C.terminal (S ω) ω) (P.restrict E) ∧
      Tendsto (fun n => ∫ ω in E, (∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
        C.supports C.weights n (S ω) ω) ∂P) atTop
        (𝓝 (∫ ω in E, (∫ z, f z ∂extendedCanonicalMass N C.terminal (S ω) ω) ∂P)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let M (n : ℕ) (t : ℝ≥0∞) (ω : Ω) := convexLevelMeasure κ B γ G (fun n => (n:ℝ))
    C.supports C.weights n t ω
  let (n : ℕ) (t : ℝ≥0∞) (ω : Ω) : IsFiniteMeasureOnCompacts (M n t ω) :=
    convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) _ C.supports C.weights n t
  let X (n : ℕ) (ω : Ω) := ∫ z, f z ∂M n (S ω) ω
  let Z (n : ℕ) (ω : Ω) := ∫ z, f z ∂M n ∞ ω
  have hXm (n : ℕ) : Measurable (X n) :=
    measurable_halfPlane_compact_test_integral _
      (convexLevelMeasure_random_time_measurable hm hBc κ γ G F hw _
        (fun n => Nat.cast_nonneg n) C.supports C.weights n S hS)
      (fun _ => inferInstance) f
  have hZm (n : ℕ) : Measurable (Z n) :=
    convexLevelMeasure_test_measurable hm hBc hκ hκ8 γ G F hw _
      (fun n => Nat.cast_nonneg n) C.supports C.weights C.weights_nonneg n ∞ f
  obtain ⟨A,hA,hbound⟩ := uniform_convexLevelMeasure_test_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg n)
    C.supports C.weights C.weights_nonneg C.weights_sum f hf 2
  have hZ (n : ℕ) := memLp_two_of_nonnegative_square_bound P (Z n) (hZm n)
    (fun _ => integral_nonneg hf) A hA (hbound n ∞)
  have hXZ (n : ℕ) (ω : Ω) : X n ω ≤ Z n ω :=
    integral_mono_measure (convexLevelMeasure_mono κ B γ G (fun n => (n:ℝ))
      C.supports C.weights n ω le_top) (ae_of_all _ hf) f.integrable
  apply integral_tendsto_of_nonnegative_L2_domination (P.restrict E) X Z _ hXm
    (fun _ _ => integral_nonneg hf) hXZ (fun n => (hZ n).1.restrict E) A.toReal
  · intro n
    exact (integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun ω => sq_nonneg (Z n ω))) (hZ n).1.integrable_sq).trans (hZ n).2
  · filter_upwards [ae_restrict_of_ae (C.all_extended_times_limit hBc hκ hκ8 F hw N hNr hpath)]
      with ω hω
    exact hω (S ω) f

lemma convexLevelMeasure_random_time_test_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (n : ℕ) (S : Ω → ℝ≥0∞) (hS : Measurable S) (E : Set Ω)
    (f : C_c(upperHalfPlane,ℝ)) :
    Integrable (fun ω => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (S ω) ω)
      (P.restrict E) := by
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  have hμm := convexLevelMeasure_random_time_measurable hm hBc κ γ G F hw u hu s w n S hS
  have hνm := convexLevelMeasure_measurable hm hBc κ γ G F hw u hu s w n ∞
  have hle := restricted_bind_le_of_ae_le P _ _ hμm hνm
    (ae_of_all _ (fun ω => convexLevelMeasure_mono κ B γ G u s w n ω le_top)) E
  rw [convexLevelMeasure_terminal_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw u hu s w hw₀ hw₁] at hle
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  exact (integrable_integral_bind_of_sections (P.restrict E) _ hμm f f.continuous.measurable
    (fun ω => by
      let := convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w n (S ω)
      exact f.integrable) (f.integrable.mono_measure hle)).1

theorem RationalCanonicalMass.random_time_test_mean_tendsto
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
    (hNr : ∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω))
    (hpath : ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => C.mass q ω)
      (C.terminal ω) (fun t => N t ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) (E : Set Ω)
    (f : C_c(upperHalfPlane,ℝ)) :
    Integrable (fun ω => ∫ z, f z ∂extendedCanonicalMass N C.terminal (S ω) ω) (P.restrict E) ∧
      Tendsto (fun n => ∫ ω in E, (∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
        C.supports C.weights n (S ω) ω) ∂P) atTop
        (𝓝 (∫ ω in E, (∫ z, f z ∂extendedCanonicalMass N C.terminal (S ω) ω) ∂P)) := by
  let fp := f ⊔ 0
  let fm := (-f) ⊔ 0
  have hp := C.random_time_nonnegative_mean_tendsto hB hBm hBc hB0 hκ hκ8 F hw hgrowth
    N hNr hpath S hS E fp (fun _ => le_sup_of_le_right le_rfl)
  have hn := C.random_time_nonnegative_mean_tendsto hB hBm hBc hB0 hκ hκ8 F hw hgrowth
    N hNr hpath S hS E fm (fun _ => le_sup_of_le_right le_rfl)
  have hsplit (ρ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts ρ] :
      (∫ z, f z ∂ρ) = (∫ z, fp z ∂ρ)-(∫ z, fm z ∂ρ) := by
    rw [← integral_sub fp.integrable fm.integrable]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => (max_zero_sub_eq_self (f z)).symm)
  let (ω : Ω) : IsFiniteMeasureOnCompacts (extendedCanonicalMass N C.terminal (S ω) ω) :=
    (extendedCanonicalMass_radon N C.terminal hNr C.terminal_radon _ _).2
  let (n : ℕ) (ω : Ω) : IsFiniteMeasureOnCompacts
      (convexLevelMeasure κ B γ G (fun n => (n:ℝ)) C.supports C.weights n (S ω) ω) :=
    convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) _ C.supports C.weights n _
  refine ⟨?_,?_⟩
  · apply (hp.1.sub hn.1).congr
    filter_upwards [] with ω
    exact (hsplit (extendedCanonicalMass N C.terminal (S ω) ω)).symm
  · have hi (g : C_c(upperHalfPlane,ℝ)) (n : ℕ) : Integrable (fun ω => ∫ z, g z
        ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ)) C.supports C.weights n (S ω) ω)
        (P.restrict E) :=
      convexLevelMeasure_random_time_test_integrable hB hBm hBc hB0 hκ hκ8 γ G F hw
        (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg n) C.supports C.weights
        C.weights_nonneg C.weights_sum n S hS E g
    simpa only [hsplit,integral_sub (hi fp _) (hi fm _),integral_sub hp.1 hn.1] using hp.2.sub hn.2

end SLEExactGauge.Multipoint

end

end OAI
