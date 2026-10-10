import OAI.Probability.SLE.Geometry.FirstHeightScaling

namespace OAI

/-! A bounded narrow first-height event, its probability uniformly over spatial
scales, and measurability of the corresponding stopped-past certificate. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.FirstHeightSupport

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def narrowRiseBy (B : ℝ) (T : ℝ≥0) : Set C(ℝ≥0, ℂ) :=
  {p | ∃ S : ℝ≥0, 0 < S ∧ S ≤ T ∧ MapsTo p (Icc 0 S) (narrowStrip B) ∧
    p S ∈ aboveQuarterHeight B}

theorem isOpen_narrowRiseBy (B : ℝ) (T : ℝ≥0) : IsOpen (narrowRiseBy B T) := by
  have he : narrowRiseBy B T = ⋃ S : ℝ≥0, ⋃ (_ : 0 < S), ⋃ (_ : S ≤ T),
      {p : C(ℝ≥0, ℂ) | MapsTo p (Icc 0 S) (narrowStrip B)} ∩
      (fun p : C(ℝ≥0, ℂ) => p S) ⁻¹' aboveQuarterHeight B := by
    ext p
    simp only [narrowRiseBy, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨S, hS, hST, hN, hV⟩ <;> exact ⟨S, hS, hST, hN, hV⟩
  rw [he]
  exact isOpen_iUnion fun S => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc
      (isOpen_lt Complex.continuous_re.abs continuous_const)).inter
      ((isOpen_lt continuous_const Complex.continuous_im).preimage (continuous_eval_const S))

theorem measurableSet_narrowRiseBy (B : ℝ) (T : ℝ≥0) : MeasurableSet (narrowRiseBy B T) :=
  (isOpen_narrowRiseBy B T).measurableSet

theorem narrowRiseEvent_eq_iUnion (B : ℝ) :
    narrowRiseEvent B = ⋃ n : ℕ, narrowRiseBy B (n + 1) := by
  ext p
  constructor
  · rintro ⟨T, hT, hN, hV⟩
    obtain ⟨n, hn⟩ := exists_nat_gt T
    exact mem_iUnion.mpr ⟨n, T, hT, hn.le.trans (by simp), hN, hV⟩
  · intro hp
    obtain ⟨n, T, hT, _, hN, hV⟩ := mem_iUnion.mp hp
    exact ⟨T, hT, hN, hV⟩

theorem scalePath_narrowRiseBy_iff
    (p : C(ℝ≥0, ℂ)) (c : ℝ≥0) (hc : 0 < c) (B : ℝ) (T : ℝ≥0) :
    ScaleTraceLaw.scalePath c p ∈ narrowRiseBy ((c : ℝ) * B) (T * c ^ 2) ↔
      p ∈ narrowRiseBy B T := by
  have hcR : 0 < (c : ℝ) := hc
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hre (t : ℝ≥0) : |(ScaleTraceLaw.scalePath c p t).re| =
      (c : ℝ) * |(p (sourceScaleTime c t)).re| := by
    change |((c : ℂ) * p (sourceScaleTime c t)).re| = _
    simp [Complex.mul_re, abs_mul, abs_of_nonneg c.coe_nonneg]
  have him (t : ℝ≥0) : (ScaleTraceLaw.scalePath c p t).im =
      (c : ℝ) * (p (sourceScaleTime c t)).im := by
    change ((c : ℂ) * p (sourceScaleTime c t)).im = _
    simp [Complex.mul_im]
  constructor
  · rintro ⟨S, hS, hST, hN, hV⟩
    refine ⟨sourceScaleTime c S, div_pos hS hc2, (div_le_iff₀ hc2).mpr hST, ?_, ?_⟩
    · intro t ht
      have hv : t * c ^ 2 ∈ Icc (0 : ℝ≥0) S :=
        ⟨bot_le, (le_div_iff₀ hc2).mp ht.2⟩
      have hh : |(ScaleTraceLaw.scalePath c p (t * c ^ 2)).re| < (c : ℝ) * B / 16 := hN hv
      rw [hre] at hh
      simp only [sourceScaleTime, mul_div_cancel_right₀ _ (ne_of_gt hc2)] at hh
      apply (mul_lt_mul_iff_right₀ hcR).mp
      nlinarith
    · have hh : (c : ℝ) * B / 4 < (ScaleTraceLaw.scalePath c p S).im := hV
      rw [him] at hh
      apply (mul_lt_mul_iff_right₀ hcR).mp
      nlinarith
  · rintro ⟨S, hS, hST, hN, hV⟩
    refine ⟨S * c ^ 2, mul_pos hS hc2, mul_le_mul_of_nonneg_right hST hc2.le, ?_, ?_⟩
    · intro t ht
      have hu : sourceScaleTime c t ∈ Icc (0 : ℝ≥0) S :=
        ⟨bot_le, (div_le_iff₀ hc2).mpr ht.2⟩
      change |(ScaleTraceLaw.scalePath c p t).re| < (c : ℝ) * B / 16
      rw [hre]
      have hh : |(p (sourceScaleTime c t)).re| < B / 16 := hN hu
      nlinarith
    · change (c : ℝ) * B / 4 < (ScaleTraceLaw.scalePath c p (S * c ^ 2)).im
      rw [him]
      simp only [sourceScaleTime, mul_div_cancel_right₀ _ (ne_of_gt hc2)]
      have hh : B / 4 < (p S).im := hV
      nlinarith

theorem narrowRiseBy_probability_scaling
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω) (γ ω) (G ω) (F ω))
    (c : ℝ≥0) (hcpos : 0 < c) (B : ℝ) (T : ℝ≥0) :
    P {ω | sourceTracePath γ (fun ω => (hw ω).1) ω ∈
      narrowRiseBy ((c : ℝ) * B) (T * c ^ 2)} =
    P {ω | sourceTracePath γ (fun ω => (hw ω).1) ω ∈ narrowRiseBy B T} := by
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  obtain ⟨Φ, hΦm, hΦ, _⟩ := sourceStoppedTraceLaw κ hκ hκ8 B₀ hB₀ hm hc γ G F hw
  have hgm : Measurable gp := by
    have he : gp = Φ ∘ sourceDriverPath B₀ hc := funext fun ω => (hΦ ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable _ hm)
  have he := congrArg (fun μ : Measure C(ℝ≥0, ℂ) =>
      μ (narrowRiseBy ((c : ℝ) * B) (T * c ^ 2)))
    (ScaleTraceLaw.scaled_trace_path_law κ hκ hκ8 B₀ hB₀ hm hc γ G F hw c hcpos)
  change (P.map (ScaleTraceLaw.scalePath c ∘ gp)) _ = (P.map gp) _ at he
  rw [Measure.map_apply ((ScaleTraceLaw.measurable_scalePath c).comp hgm)
      (measurableSet_narrowRiseBy _ _),
    Measure.map_apply hgm (measurableSet_narrowRiseBy _ _)] at he
  have hset : {ω | ScaleTraceLaw.scalePath c (gp ω) ∈
      narrowRiseBy ((c : ℝ) * B) (T * c ^ 2)} = {ω | gp ω ∈ narrowRiseBy B T} := by
    ext ω
    exact scalePath_narrowRiseBy_iff (gp ω) c hcpos B T
  change P {ω | ScaleTraceLaw.scalePath c (gp ω) ∈
      narrowRiseBy ((c : ℝ) * B) (T * c ^ 2)} =
      P {ω | gp ω ∈ narrowRiseBy ((c : ℝ) * B) (T * c ^ 2)} at he
  rw [hset] at he
  exact he.symm

/-- The uniform probability can be realized before a deterministic multiple
of the square of the spatial scale. -/
theorem uniform_bounded_narrowRise_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedGeometricTubeSupport P γ) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ q : ℝ≥0∞, 0 < q ∧ ∀ c : ℝ≥0, 0 < c →
      q ≤ P {ω | sourceTracePath γ (fun ω => (hw ω).1) ω ∈
        narrowRiseBy (c : ℝ) (T₀ * c ^ 2)} := by
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hpos : 0 < P {ω | gp ω ∈ narrowRiseEvent 1} :=
    narrowRiseEvent_positive P γ hpublished zero_lt_one
  have hex : ∃ n : ℕ, 0 < P {ω | gp ω ∈ narrowRiseBy 1 (n + 1)} := by
    by_contra! hn
    have he : {ω | gp ω ∈ narrowRiseEvent 1} =
        ⋃ n : ℕ, {ω | gp ω ∈ narrowRiseBy 1 (n + 1)} := by
      ext ω
      simp only [narrowRiseEvent_eq_iUnion, mem_ofPred_eq, mem_iUnion]
    rw [he, measure_iUnion_null (fun n => le_antisymm (hn n) bot_le)] at hpos
    exact (lt_irrefl _) hpos
  obtain ⟨n, hn⟩ := hex
  refine ⟨n + 1, by positivity, P {ω | gp ω ∈ narrowRiseBy 1 (n + 1)}, hn, ?_⟩
  intro c hcpos
  have he := narrowRiseBy_probability_scaling κ hκ hκ8 B₀ hB₀ hm hc γ G F hw c hcpos 1 (n + 1)
  simpa only [mul_one] using he.symm.le

/-- Stop a continuous trace at a finite stopping time, retaining a continuous
path on the common nonnegative-time domain. -/
def stoppedTracePath {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (hc : ∀ ω, Continuous (γ ω))
    (σ : Ω → ℝ≥0) (ω : Ω) : C(ℝ≥0, ℂ) :=
  ⟨fun t => γ ω (min t (σ ω)), (hc ω).comp (continuous_id.min continuous_const)⟩

/-- Every coordinate of this path is already measurable in the stopped past. -/
theorem stoppedTracePath_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω)) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0))) :
    Measurable[hσ.measurableSpace] (stoppedTracePath γ hc σ) := by
  have hp := ha.stronglyAdapted.isStronglyProgressive_of_continuous hc
  let : MeasurableSpace Ω := hσ.measurableSpace
  apply source_path_measurable
  intro t
  have hm := measurable_stoppedValue hp (hσ.min_const t)
  have hm' := hm.mono (IsStoppingTime.measurableSpace_mono (hσ.min_const t) hσ
    (fun _ => min_le_left _ _)) le_rfl
  change Measurable[hσ.measurableSpace]
    (fun ω => γ ω ((min (σ ω : WithTop ℝ≥0) (t : WithTop ℝ≥0)).untopA)) at hm'
  change Measurable[hσ.measurableSpace] (fun ω => γ ω (min t (σ ω)))
  simpa only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, min_comm] using hm'

/-- This concrete certificate depends only on the stopped trace. Its height
and horizontal-strip conditions can therefore be tested in the stopped past. -/
def stoppedNarrowCertificate {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (σ : Ω → ℝ≥0)
    (B : ℝ) (T : ℝ≥0) : Set Ω :=
  {ω | 0 < σ ω ∧ (γ ω (σ ω)).im = B / 4 ∧
    MapsTo (fun t => γ ω (min t (σ ω))) (Icc 0 T) (narrowStrip B)}

theorem stoppedNarrowCertificate_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω)) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0))) (B : ℝ) (T : ℝ≥0) :
    MeasurableSet[hσ.measurableSpace] (stoppedNarrowCertificate γ σ B T) := by
  have hp := ha.stronglyAdapted.isStronglyProgressive_of_continuous hc
  have hv : Measurable[hσ.measurableSpace] (fun ω => γ ω (σ ω)) := by
    have hm := measurable_stoppedValue hp hσ
    change Measurable[hσ.measurableSpace]
      (fun ω => γ ω ((σ ω : WithTop ℝ≥0).untopA)) at hm
    simpa only [WithTop.untopA, WithTop.untopD_coe] using hm
  have hs : Measurable[hσ.measurableSpace] σ := by
    simpa only [WithTop.untopA, WithTop.untopD_coe] using hσ.measurable.untopA
  have hpath := stoppedTracePath_measurable ℱ γ ha hc σ hσ
  exact (measurableSet_lt measurable_const hs).inter
    ((measurableSet_eq_fun (Complex.continuous_im.measurable.comp hv) measurable_const).inter
      ((ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc
        (isOpen_lt Complex.continuous_re.abs continuous_const)).measurableSet.preimage hpath))

/-- Finite first-height clock, stopped at the prescribed deterministic bound. -/
def boundedFirstHeightTime (γ : ℝ≥0 → ℂ) (B : ℝ) (T : ℝ≥0) : ℝ≥0 :=
  (min (firstHeightTime γ (B / 4)) (T : WithTop ℝ≥0)).untopD 0

@[simp] theorem boundedFirstHeightTime_coe (γ : ℝ≥0 → ℂ) (B : ℝ) (T : ℝ≥0) :
    (boundedFirstHeightTime γ B T : WithTop ℝ≥0) =
      min (firstHeightTime γ (B / 4)) (T : WithTop ℝ≥0) := by
  cases he : firstHeightTime γ (B / 4) with
  | top =>
    simp only [boundedFirstHeightTime, he, min_eq_right le_top, WithTop.untopD_coe]
  | coe r =>
    simp only [boundedFirstHeightTime, he, ← WithTop.coe_min, WithTop.untopD_coe]

theorem boundedFirstHeightTime_le (γ : ℝ≥0 → ℂ) (B : ℝ) (T : ℝ≥0) :
    boundedFirstHeightTime γ B T ≤ T := by
  apply WithTop.coe_le_coe.mp
  rw [boundedFirstHeightTime_coe]
  exact min_le_right _ _

theorem boundedFirstHeightTime_isStoppingTime
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω)) (B : ℝ) (T : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (boundedFirstHeightTime (γ ω) B T : WithTop ℝ≥0)) := by
  simpa only [boundedFirstHeightTime_coe] using
    (firstHeightTime_isStoppingTime ℱ γ ha hc (B / 4)).min_const T

/-- A bounded supported rise supplies a narrow certificate at the actual
first-height clock. -/
theorem narrowRiseBy_gives_bounded_certificate
    {B : ℝ} (hB : 0 < B) (p : C(ℝ≥0, ℂ)) (hp0 : p 0 = 0)
    {T : ℝ≥0} (hp : p ∈ narrowRiseBy B T) :
    let σ := boundedFirstHeightTime p B T
    0 < σ ∧ (p σ).im = B / 4 ∧
      MapsTo (fun t => p (min t σ)) (Icc 0 T) (narrowStrip B) := by
  obtain ⟨S, _, hST, hstrip, habove⟩ := hp
  obtain ⟨τ, htime, hτ, hτS, hhit, _⟩ :=
    exists_first_height p p.continuous hp0 (by positivity : 0 < B / 4) habove
  have hσ : boundedFirstHeightTime p B T = τ := by
    apply WithTop.coe_injective
    rw [boundedFirstHeightTime_coe, htime, min_eq_left (WithTop.coe_le_coe.mpr (hτS.le.trans hST))]
  dsimp only
  rw [hσ]
  refine ⟨hτ, hhit, ?_⟩
  intro t _
  exact hstrip ⟨bot_le, (min_le_right t τ).trans hτS.le⟩

/-- Every measurable bounded certificate gives the full first-height
geometry, including strict freshness and rectangle containment. -/
theorem bounded_certificate_geometry
    (p : C(ℝ≥0, ℂ)) (hp0 : p 0 = 0) (hpH : ∀ t, 0 ≤ (p t).im)
    {B : ℝ} (hB : 0 < B) (T : ℝ≥0)
    (hcert : let σ := boundedFirstHeightTime p B T
      0 < σ ∧ (p σ).im = B / 4 ∧
        MapsTo (fun t => p (min t σ)) (Icc 0 T) (narrowStrip B)) :
    let σ := boundedFirstHeightTime p B T
    firstHeightTime p (B / 4) = (σ : WithTop ℝ≥0) ∧ 0 < σ ∧
      (p σ).im = B / 4 ∧ |(p σ).re| < B / 16 ∧
      (∀ u : ℝ≥0, u < σ → (p u).im < (p σ).im) ∧
      p '' Icc 0 σ ⊆ GuideSplice.closedInitialRectangle B := by
  let σ := boundedFirstHeightTime p B T
  obtain ⟨hσpos, hhit, hstrip⟩ := hcert
  change (p σ).im = B / 4 at hhit
  change MapsTo (fun t => p (min t σ)) (Icc 0 T) (narrowStrip B) at hstrip
  have hσT : σ ≤ T := boundedFirstHeightTime_le p B T
  have hfirstle : firstHeightTime p (B / 4) ≤ (σ : WithTop ℝ≥0) := by
    apply hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ σ from bot_le)
    change (p σ).im - B / 4 = 0
    rw [hhit, sub_self]
  have htime : firstHeightTime p (B / 4) = (σ : WithTop ℝ≥0) := by
    apply le_antisymm hfirstle
    exact (boundedFirstHeightTime_coe p B T).trans_le (min_le_left _ _)
  have hprior (u : ℝ≥0) (hu : u < σ) : (p u).im < B / 4 := by
    by_contra hn
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ u from bot_le)
      (Complex.continuous_im.comp p.continuous).continuousOn
      (show B / 4 ∈ Icc (p 0).im (p u).im by
        rw [hp0, Complex.zero_im]
        exact ⟨by positivity, le_of_not_gt hn⟩)
    have hh : firstHeightTime p (B / 4) ≤ (v : WithTop ℝ≥0) := by
      apply hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ v from bot_le)
      change (p v).im - B / 4 = 0
      rw [show (p v).im = B / 4 from he, sub_self]
    rw [htime, WithTop.coe_le_coe] at hh
    exact (not_le_of_gt hu) (hh.trans hv.2)
  have hσstrip : |(p σ).re| < B / 16 := by
    simpa only [min_self, narrowStrip, mem_ofPred_eq] using hstrip ⟨bot_le, hσT⟩
  refine ⟨htime, hσpos, hhit, hσstrip, ?_, ?_⟩
  · intro u hu
    rw [hhit]
    exact hprior u hu
  · rintro z ⟨u, hu, rfl⟩
    have hs : |(p u).re| < B / 16 := by
      have hh := hstrip ⟨bot_le, hu.2.trans hσT⟩
      change |(p (min u σ)).re| < B / 16 at hh
      rw [min_eq_left (show u ≤ σ from hu.2)] at hh
      exact hh
    refine ⟨hs.le, hpH u, ?_⟩
    rcases eq_or_lt_of_le hu.2 with rfl | huσ
    · exact hhit.le
    · exact (hprior u huσ).le

theorem bounded_certificate_gives_first_height
    (p : C(ℝ≥0, ℂ)) (hp0 : p 0 = 0) (hpH : ∀ t, 0 ≤ (p t).im)
    {B : ℝ} (hB : 0 < B) (T : ℝ≥0)
    (hcert : let σ := boundedFirstHeightTime p B T
      0 < σ ∧ (p σ).im = B / 4 ∧
        MapsTo (fun t => p (min t σ)) (Icc 0 T) (narrowStrip B)) :
    NarrowFirstHeight B p :=
  ⟨boundedFirstHeightTime p B T, bounded_certificate_geometry p hp0 hpH hB T hcert⟩

/-- Uniform bounded first-height probability in the form of a concrete
stopped-past event. -/
theorem uniform_boundedFirstHeight_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedGeometricTubeSupport P γ) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ q : ℝ≥0∞, 0 < q ∧ ∀ c : ℝ≥0, 0 < c →
      q ≤ P (stoppedNarrowCertificate γ
        (fun ω => boundedFirstHeightTime (γ ω) c (T₀ * c ^ 2)) c (T₀ * c ^ 2)) := by
  obtain ⟨T₀, hT₀, q, hq, hprob⟩ := uniform_bounded_narrowRise_probability
    κ hκ hκ8 B₀ hB₀ hm hc γ G F hw hpublished
  refine ⟨T₀, hT₀, q, hq, fun c hcpos => (hprob c hcpos).trans ?_⟩
  apply measure_mono
  intro ω hω
  exact narrowRiseBy_gives_bounded_certificate hcpos
    (sourceTracePath γ (fun ω => (hw ω).1) ω) (hw ω).2.1 hω

/-- The event in the uniform probability theorem is measurable at its
bounded first-height stopping time. -/
theorem boundedFirstHeight_certificate_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω)) (B : ℝ) (T : ℝ≥0) :
    MeasurableSet[(boundedFirstHeightTime_isStoppingTime ℱ γ ha hc B T).measurableSpace]
      (stoppedNarrowCertificate γ (fun ω => boundedFirstHeightTime (γ ω) B T) B T) :=
  stoppedNarrowCertificate_measurable ℱ γ ha hc
    (fun ω => boundedFirstHeightTime (γ ω) B T)
    (boundedFirstHeightTime_isStoppingTime ℱ γ ha hc B T) B T

/-- The same event is measurable in the full first-height past, as used in
the manuscript's conditional continuation argument. -/
theorem boundedFirstHeight_certificate_measurable_at_first
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω)) (B : ℝ) (T : ℝ≥0) :
    MeasurableSet[(firstHeightTime_isStoppingTime ℱ γ ha hc (B / 4)).measurableSpace]
      (stoppedNarrowCertificate γ (fun ω => boundedFirstHeightTime (γ ω) B T) B T) := by
  have hle := IsStoppingTime.measurableSpace_mono
    (boundedFirstHeightTime_isStoppingTime ℱ γ ha hc B T)
    (firstHeightTime_isStoppingTime ℱ γ ha hc (B / 4))
    (fun ω => (boundedFirstHeightTime_coe (γ ω) B T).trans_le (min_le_left _ _))
  exact hle _ (boundedFirstHeight_certificate_measurable ℱ γ ha hc B T)

end SLEExactGauge.FirstHeightSupport

end

end OAI
