import OAI.Probability.SLE.Mass.LevelRemainderSupport
import OAI.Probability.SLE.Mass.RationalMassFromSupports
import OAI.Probability.SLE.Mass.CountableLevelAdapted
import OAI.Probability.SLE.Mass.LevelRadonNonatomic

namespace OAI

/-! The actual common convex-tail construction at rational times, with
adapted versions, positive trace increments and its conditional Green kernel. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def rationalMassTime (n : ℕ) : ℝ≥0 :=
  (((Encodable.decode (α := ℚ) n).getD 0 : ℚ) : ℝ).toNNReal

@[simp] lemma rationalMassTime_encode (q : ℚ) :
    rationalMassTime (Encodable.encode q) = (q : ℝ).toNNReal := by
  simp only [rationalMassTime,Encodable.encodek,Option.getD_some]

structure RationalCanonicalMass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hBm : Measurable (Function.uncurry B))
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) where
  terminal : Ω → Measure upperHalfPlane
  mass : ℚ → Ω → Measure upperHalfPlane
  terminal_measurable : Measurable terminal
  mass_measurable : ∀ q : ℚ, Measurable[Filtration.natural B (fun r =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)
      (q : ℝ).toNNReal] (mass q)
  terminal_radon : ∀ ω, (terminal ω).Regular ∧ IsFiniteMeasureOnCompacts (terminal ω)
  mass_radon : ∀ q ω, (mass q ω).Regular ∧ IsFiniteMeasureOnCompacts (mass q ω)
  supports : ℕ → Finset ℕ
  weights : ℕ → ℕ → ℝ
  weights_nonneg : ∀ n i, i ∈ supports n → 0 ≤ weights n i
  weights_sum : ∀ n, ∑ i ∈ supports n, weights n i = 1
  terminal_limit : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
    Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
      supports weights n ∞ ω) atTop (𝓝 (∫ z, f z ∂terminal ω))
  mass_limit : ∀ᵐ ω ∂P, ∀ (q : ℚ) (f : C_c(upperHalfPlane,ℝ)),
    Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
      supports weights n (q : ℝ).toNNReal ω) atTop (𝓝 (∫ z, f z ∂mass q ω))
  zero : ∀ᵐ ω ∂P, mass 0 ω = 0
  increments : ∀ᵐ ω ∂P,
    HalfPlaneTraceIncrements (fun q => mass q ω) (terminal ω) (fun r => γ ω r.toNNReal)
  nonatomic : ∀ᵐ ω ∂P, NullSingletonClass (terminal ω)
  moments : ∀ K : Set upperHalfPlane, IsCompact K → ∀ m : ℕ,
    (∫⁻ ω, terminal ω K ^ m ∂P) < ∞
  mean : P.bind terminal = initialGreenMeasure κ
  conditional : ∀ q : ℚ, ∀ E : Set Ω,
    MeasurableSet[Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)
        (q : ℝ).toNNReal] E →
    (P.restrict E).bind terminal = (P.restrict E).bind (mass q) +
      (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G (q : ℝ).toNNReal)

theorem exists_rationalCanonicalMass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) :
    Nonempty (RationalCanonicalMass P κ B hBm γ G) := by
  obtain ⟨s,w,ν,η,hw₀,hw₁,hνm,hν,hlim,hηm,hη,hηsum,hmean,hkernel⟩ :=
    exists_countable_radon_remainder_kernels hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      rationalMassTime
  have hfiniteLimit : ∀ᵐ ω ∂P, ∀ j (f : C_c(upperHalfPlane,ℝ)),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
        s w n (rationalMassTime j) ω) atTop (𝓝 (∫ z, f z ∂ν (j+1) ω)) := by
    filter_upwards [hlim] with ω hω
    intro j f
    simpa only [levelMassTimes_succ] using hω (j+1) f
  obtain ⟨M,hMm,hMr,hMeq⟩ := countable_level_limits_have_past_versions P
    (fun r => hBm.comp (measurable_const.prodMk measurable_id)) hBc hκ hκ8 γ G F hw
    (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg n) s w hw₀ rationalMassTime
    (fun j => ν (j+1)) (Eventually.of_forall (fun ω j => (hν (j+1) ω).1)) hfiniteLimit
  let μ (q : ℚ) := M (Encodable.encode q)
  have hμeq : ∀ᵐ ω ∂P, ∀ q, μ q ω = ν (Encodable.encode q+1) ω := by
    filter_upwards [hMeq] with ω hω
    exact fun q => hω _
  have hμlim : ∀ᵐ ω ∂P, ∀ (q : ℚ) (f : C_c(upperHalfPlane,ℝ)),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
        s w n (q:ℝ).toNNReal ω) atTop (𝓝 (∫ z, f z ∂μ q ω)) := by
    filter_upwards [hfiniteLimit,hμeq] with ω hl he
    intro q f
    rw [he q]
    simpa only [rationalMassTime_encode] using hl (Encodable.encode q) f
  have htermLimit : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
        s w n ∞ ω) atTop (𝓝 (∫ z, f z ∂ν 0 ω)) := by
    filter_upwards [hlim] with ω hω
    exact hω 0
  have hfuture (j : ℕ) := ae_remainder_carried_by_surviving hB hBm hBc hB0 hκ hκ8 γ G F hw
    (rationalMassTime j) (η j) (hηm j) (fun ω => (hη j ω).2) (hkernel j)
  have hinc : ∀ᵐ ω ∂P,
      HalfPlaneTraceIncrements (fun q => μ q ω) (ν 0 ω) (fun r => γ ω r.toNNReal) := by
    filter_upwards [hμlim,htermLimit,hμeq,hηsum,ae_all_iff.mpr hfuture] with ω hl ht he hs hf
    let : (ν 0 ω).Regular := (hν 0 ω).1
    let (q : ℚ) : (μ q ω).Regular := (hMr (Encodable.encode q) ω).1
    let (q : ℚ) : IsFiniteMeasureOnCompacts (μ q ω) := (hMr (Encodable.encode q) ω).2
    let (n : ℕ) (v : ℝ≥0∞) : IsFiniteMeasureOnCompacts
        (convexLevelMeasure κ B γ G (fun n => (n:ℝ)) s w n v ω) :=
      convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) _ s w n v
    have hdom (q : ℚ) : μ q ω ≤ ν 0 ω := by
      apply radon_limits_mono _ _ _ _ (hl q) ht
      intro n
      exact convexLevelMeasure_mono κ B γ G (fun n => (n:ℝ)) s w n ω le_top
    have hmono : Monotone (fun q => μ q ω) := by
      intro p q hpq
      let (n : ℕ) : IsFiniteMeasureOnCompacts
          (convexLevelMeasure κ B γ G (fun n => (n:ℝ)) s w n (p:ℝ).toNNReal ω) :=
        convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) _ s w n _
      apply radon_limits_mono _ _ _ _ (hl p) (hl q)
      intro n
      exact convexLevelMeasure_mono κ B γ G (fun n => (n:ℝ)) s w n ω
        (ENNReal.coe_le_coe.mpr (Real.toNNReal_mono (Rat.cast_le.mpr hpq)))
    have hzero (q : ℚ) (hq : q ≤ 0) : μ q ω = 0 := by
      apply convex_level_radon_limit_zero_at_zero ω (hBc ω) (hw ω) (fun n => (n:ℝ))
        tendsto_natCast_atTop_atTop s w (μ q ω)
      simpa only [Real.toNNReal_eq_zero.mpr (Rat.cast_nonpos.mpr hq),ENNReal.coe_zero] using hl q
    apply halfPlaneTraceIncrements_of_past_and_future (fun q => μ q ω) (ν 0 ω) (γ ω)
      (fun q => (hMr (Encodable.encode q) ω).1) hdom hmono hzero
    · intro q _
      exact convex_level_radon_limit_carried_by_past ω (hBc ω) (hw ω) _ (fun n => (n:ℝ))
        tendsto_natCast_atTop_atTop s w (μ q ω) (hl q)
    · intro q _
      have heη : η (Encodable.encode q) ω = ν 0 ω-μ q ω := by
        apply (Measure.add_left_inj (μ q ω) _ _).mp
        rw [sigmaFinite_sub_add_cancel_of_le (hdom q),he q]
        exact hs _
      rw [← heη]
      simpa only [rationalMassTime_encode] using hf (Encodable.encode q)
  refine ⟨{
    terminal := ν 0
    mass := μ
    terminal_measurable := hνm 0
    mass_measurable := ?_
    terminal_radon := hν 0
    mass_radon := fun q => hMr (Encodable.encode q)
    supports := s
    weights := w
    weights_nonneg := hw₀
    weights_sum := hw₁
    terminal_limit := htermLimit
    mass_limit := hμlim
    zero := ?_
    increments := hinc
    nonatomic := ?_
    moments := ?_
    mean := hmean
    conditional := ?_ }⟩
  · intro q
    simpa +instances only [rationalMassTime_encode,Function.comp_def,Function.uncurry] using hMm (Encodable.encode q)
  · filter_upwards [hμlim] with ω hω
    let : (μ 0 ω).Regular := (hMr (Encodable.encode (0:ℚ)) ω).1
    apply convex_level_radon_limit_zero_at_zero ω (hBc ω) (hw ω) (fun n => (n:ℝ))
      tendsto_natCast_atTop_atTop s w (μ 0 ω)
    simpa only [Rat.cast_zero,Real.toNNReal_zero,ENNReal.coe_zero] using hω 0
  · exact level_radon_limit_nonatomic hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg n) s w hw₀ hw₁ ∞ (ν 0) (hνm 0)
      (fun ω => (hν 0 ω).2) htermLimit
  · intro K hK m
    exact level_radon_limit_compact_moments hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg n) s w hw₀ hw₁ ∞ (ν 0)
      (fun ω => (hν 0 ω).2) htermLimit K hK m
  · intro q E hE
    have hμm : Measurable (μ q) := (hMm (Encodable.encode q)).mono (Filtration.le _ _) le_rfl
    have hs : ∀ᵐ ω ∂P, η (Encodable.encode q) ω + μ q ω = ν 0 ω := by
      filter_upwards [hμeq,hηsum] with ω he hs
      rw [he q]
      exact hs _
    have hc := bind_add_of_ae (P.restrict E) (μ q) (ν 0) (η (Encodable.encode q))
      hμm (hνm 0) (hηm _) (ae_restrict_of_ae hs)
    rw [← hc,add_comm]
    congr 1
    simpa only [rationalMassTime_encode] using hkernel (Encodable.encode q) E (by simpa +instances only [rationalMassTime_encode] using hE)

end SLEExactGauge.Multipoint

end

end OAI
