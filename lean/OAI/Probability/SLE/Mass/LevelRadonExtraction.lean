import OAI.Probability.SLE.Mass.HalfPlaneLevelMeasures
import OAI.Probability.SLE.Mass.RadonTestFamily
import OAI.Probability.SLE.Mass.L2MeanConvergence

namespace OAI

/-! One sequence of convex level measures converges vaguely at every
prescribed countable time, on one event of probability one. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def convexLevelMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (u : ℕ → ℝ)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (n : ℕ) (t : ℝ≥0∞) (ω : Ω) :
    Measure upperHalfPlane :=
  ∑ i ∈ s n, ENNReal.ofReal (w n i) • halfPlaneLevelMeasure κ B γ G (u (n+i)) t ω

lemma convexLevelMeasure_finite_on_compacts
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (ω : Ω) (hBc : Continuous (fun t => B t ω))
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (n : ℕ) (t : ℝ≥0∞) :
    IsFiniteMeasureOnCompacts (convexLevelMeasure κ B γ G u s w n t ω) := by
  constructor
  intro K hK
  rw [convexLevelMeasure,Measure.finsetSum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  rw [Measure.smul_apply,smul_eq_mul]
  let := halfPlaneLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω hBc hw (u (n+i)) t
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

lemma integral_convexLevelMeasure
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (ω : Ω) (hBc : Continuous (fun t => B t ω))
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (n : ℕ) (t : ℝ≥0∞)
    (hw₀ : ∀ i ∈ s n, 0 ≤ w n i) (f : C_c(upperHalfPlane,ℝ)) :
    (∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω) =
      ∑ i ∈ s n, w n i * levelApproximationRealTest κ B γ G (u (n+i)) t (extendHalfPlaneTest f) ω := by
  have hi (i : ℕ) : Integrable f
      (ENNReal.ofReal (w n i) • halfPlaneLevelMeasure κ B γ G (u (n+i)) t ω) := by
    let := halfPlaneLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω hBc hw (u (n+i)) t
    let : IsFiniteMeasureOnCompacts
        (ENNReal.ofReal (w n i) • halfPlaneLevelMeasure κ B γ G (u (n+i)) t ω) :=
      IsFiniteMeasureOnCompacts.smul
        (halfPlaneLevelMeasure κ B γ G (u (n+i)) t ω) ENNReal.ofReal_ne_top
    exact f.integrable
  rw [convexLevelMeasure,integral_finsetSum_measure (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i his
  rw [integral_smul_measure,ENNReal.toReal_ofReal (hw₀ i his),smul_eq_mul,
    integral_halfPlaneLevelMeasure]

theorem exists_common_halfPlane_test_limits_with_pairings
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (f : ℕ → C_c(upperHalfPlane,ℝ)) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (t : ℕ → ℝ≥0∞) :
    ∃ x : ℕ → Lp ℝ 2 P, ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Tendsto (fun n => ∫ ω, (∫ z, f j z ∂convexLevelMeasure κ B γ G u s w n (t j) ω) ∂P)
        atTop (𝓝 (∫ ω, x j ω ∂P))) ∧
      (∀ j (a : Ω → ℝ), MemLp a 2 P →
        Tendsto (fun n => ∫ ω, a ω * (∫ z, f j z ∂convexLevelMeasure κ B γ G u s w n (t j) ω) ∂P)
          atTop (𝓝 (∫ ω, a ω * x j ω ∂P))) ∧
      (∀ᵐ ω ∂P, ∀ j, Tendsto (fun n => ∫ z, f j z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
        atTop (𝓝 (x j ω))) := by
  let φ (j : ℕ) := extendHalfPlaneTest (f j)
  let K (j : ℕ) := (Subtype.val : upperHalfPlane → ℂ) '' tsupport (f j)
  have hK (j : ℕ) : IsCompact (K j) := (f j).hasCompactSupport.image continuous_subtype_val
  have hKH (j : ℕ) : K j ⊆ upperHalfPlane := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hφ (j : ℕ) : Measurable (φ j) := extendHalfPlaneTest_measurable _ (f j).continuous.measurable
  have info (j : ℕ) := uniform_signed_levelTest_L2 hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
    (K j) (hK j) (hKH j) (φ j) (hφ j) ‖(f j).toBoundedContinuousFunction‖
    (fun z _ => extendHalfPlaneTest_norm_le _ z) (extendHalfPlaneTest_support (f j))
  let A (n j : ℕ) := levelApproximationRealTest κ B γ G (u n) (t j) (φ j)
  have hLp (n j : ℕ) : MemLp (A n j) 2 P := (info j).1 (u n) (hu n) (t j)
  have hbound (j : ℕ) : ∃ D : ℝ, ∀ n, ‖(hLp n j).toLp (A n j)‖ ≤ D := by
    obtain ⟨D,hD⟩ := (info j).2
    exact ⟨D,fun n => hD (u n) (hu n) (t j) (hLp n j)⟩
  obtain ⟨x,s,w,hw₀,hw₁,hL2,hc⟩ := exists_randomVariable_convex_tail_limit A hLp hbound
  refine ⟨x,s,w,hw₀,hw₁,?_,?_,?_⟩
  · intro j
    let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    have hmean := weighted_randomVariable_integral_tendsto P (fun n => A n j)
      (fun n => hLp n j) s w (x j) (hL2 j)
    convert hmean using 1
    funext n
    apply integral_congr_ae
    filter_upwards [] with ω
    exact integral_convexLevelMeasure hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w n (t j)
      (hw₀ n) (f j)
  · intro j a ha
    have hmean := weighted_randomVariable_pairing_tendsto P (fun n => A n j)
      (fun n => hLp n j) s w (x j) (hL2 j) a ha
    convert hmean using 1
    funext n
    apply integral_congr_ae
    filter_upwards [] with ω
    apply congrArg (fun v : ℝ => a ω * v)
    exact integral_convexLevelMeasure hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w n (t j)
      (hw₀ n) (f j)
  · filter_upwards [hc] with ω hω
    intro j
    simpa only [integral_convexLevelMeasure hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w _ _
      (hw₀ _) (f j),A,φ] using hω j

theorem exists_common_halfPlane_test_limits
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (f : ℕ → C_c(upperHalfPlane,ℝ)) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (t : ℕ → ℝ≥0∞) :
    ∃ x : ℕ → Lp ℝ 2 P, ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Tendsto (fun n => ∫ ω, (∫ z, f j z ∂convexLevelMeasure κ B γ G u s w n (t j) ω) ∂P)
        atTop (𝓝 (∫ ω, x j ω ∂P))) ∧
      (∀ᵐ ω ∂P, ∀ j, Tendsto (fun n => ∫ z, f j z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
        atTop (𝓝 (x j ω))) := by
  obtain ⟨x,s,w,hw₀,hw₁,hm,_,ha⟩ := exists_common_halfPlane_test_limits_with_pairings
    hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth f u hu t
  exact ⟨x,s,w,hw₀,hw₁,hm,ha⟩

/-- The same convex level measures have one Radon limit at all times in
an arbitrary countable list. The spatial determining family is constructed,
and is not an additional input. -/
theorem exists_common_level_radon_limits
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (t : ℕ → ℝ≥0∞) :
    ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ᵐ ω ∂P, ∃ ν : ℕ → Measure upperHalfPlane,
        (∀ j, (ν j).Regular ∧ IsFiniteMeasureOnCompacts (ν j)) ∧
        ∀ j (f : C_c(upperHalfPlane,ℝ)),
          Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
            atTop (𝓝 (∫ z, f z ∂ν j))) := by
  let D := localTestFamily upperHalfPlane
  obtain ⟨x,s,w,hw₀,hw₁,_,hconv⟩ := exists_common_halfPlane_test_limits hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth (fun j => D.test (Nat.unpair j).2) u hu (fun j => t (Nat.unpair j).1)
  refine ⟨s,w,hw₀,hw₁,?_⟩
  filter_upwards [hconv] with ω hω
  have hex (j : ℕ) : ∃ ν : Measure upperHalfPlane, ν.Regular ∧ IsFiniteMeasureOnCompacts ν ∧
      ∀ f : C_c(upperHalfPlane,ℝ),
        Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
          atTop (𝓝 (∫ z, f z ∂ν)) := by
    let (n : ℕ) : IsFiniteMeasureOnCompacts (convexLevelMeasure κ B γ G u s w n (t j) ω) :=
      convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w n (t j)
    apply D.exists_radon_limit
    intro k
    refine ⟨x (Nat.pair j k) ω,?_⟩
    simpa only [Nat.unpair_pair] using hω (Nat.pair j k)
  choose ν hν using hex
  exact ⟨ν,fun j => ⟨(hν j).1,(hν j).2.1⟩,fun j => (hν j).2.2⟩

end SLEExactGauge.Multipoint

end

end OAI
