import OAI.Probability.SLE.Geometry.FirstHeightBounded
import OAI.Probability.SLE.Geometry.RandomBoundaryTubes
import OAI.Probability.SLE.StripProbabilities

namespace OAI

/-! Early physical containment of the narrow first-height past. The event
is measurable in the stopped past, and failure is an actual conformal
localization escape event. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.EarlyPassageLocalization

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace

open FirstHeightSupport

/-- Physical containment of the entire trace segment through a finite stop. -/
def stoppedImageEvent {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (σ : Ω → ℝ≥0)
    (Fbar : ℂ → OnePoint ℂ) (a : ℂ) (r : ℝ) : Set Ω :=
  {ω | ∀ t ∈ Icc 0 (σ ω), Fbar (γ ω t) ∈
    (fun z : ℂ => (z : OnePoint ℂ)) '' ball a r}

theorem stoppedImageEvent_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω)) (hH : ∀ ω t, 0 ≤ (γ ω t).im)
    (σ : Ω → ℝ≥0) (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hT : ∀ ω, σ ω ≤ T)
    (Fbar : ℂ → OnePoint ℂ) (hFbar : ContinuousOn Fbar closedHalfPlane)
    (a : ℂ) (r : ℝ) :
    MeasurableSet[hσ.measurableSpace] (stoppedImageEvent γ σ Fbar a r) := by
  let f : C(closedHalfPlane, OnePoint ℂ) := ⟨fun z => Fbar z, hFbar.domRestrict⟩
  let p := stoppedTracePath γ hc σ
  have hp : Measurable[hσ.measurableSpace] p :=
    stoppedTracePath_measurable ℱ γ ha hc σ hσ
  have hpm : Measurable[hσ.measurableSpace] (fun ω => f.comp (liftClosedPath (p ω))) := by
    exact (ContinuousMap.continuous_postcomp f).measurable.comp
      (measurable_liftClosedPath.comp hp)
  have hO : IsOpen ((fun z : ℂ => (z : OnePoint ℂ)) '' ball a r) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
  have he : stoppedImageEvent γ σ Fbar a r =
      {ω | MapsTo (f.comp (liftClosedPath (p ω))) (Icc 0 T)
        ((fun z : ℂ => (z : OnePoint ℂ)) '' ball a r)} := by
    ext ω
    have hpc : ClosedPathProperty (p ω) := fun t => hH ω (min t (σ ω))
    have heval (t : ℝ≥0) : f.comp (liftClosedPath (p ω)) t =
        Fbar (γ ω (min t (σ ω))) := by
      change Fbar ((liftClosedPath (p ω) t : closedHalfPlane) : ℂ) = _
      rw [liftClosedPath_apply _ hpc]
      rfl
    constructor
    · intro h t ht
      rw [heval]
      exact h _ ⟨bot_le, min_le_right _ _⟩
    · intro h t ht
      have hh := h ⟨bot_le, ht.2.trans (hT ω)⟩
      simpa only [heval, min_eq_left ht.2] using hh
  rw [he]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hO).measurableSet.preimage hpm

/-- Containment failure before a bounded parameter-radius stop is exactly
an escape covered by conformal localization. -/
theorem stoppedImage_failure_subset_escape
    {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (σ : Ω → ℝ≥0)
    (E : Set Ω) (Fbar : ℂ → OnePoint ℂ) (a : ℂ) (r A : ℝ)
    (hbound : ∀ ω ∈ E, ∀ t ∈ Icc 0 (σ ω), ‖γ ω t‖ < A) :
    E \ stoppedImageEvent γ σ Fbar a r ⊆
      {ω | ∃ t : ℝ≥0, BeforeFirstModulus (γ ω) A t ∧
        Fbar (γ ω t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' ball a r} := by
  rintro ω ⟨hE, hbad⟩
  change ¬ ∀ t ∈ Icc 0 (σ ω), Fbar (γ ω t) ∈
    (fun z : ℂ => (z : OnePoint ℂ)) '' ball a r at hbad
  push Not at hbad
  obtain ⟨t, ht, hbad⟩ := hbad
  refine ⟨t, ?_, hbad⟩
  intro s hs
  exact hbound ω hE s ⟨bot_le, hs.le.trans ht.2⟩

/-- A bounded first-height certificate stays strictly inside the ball of
half the rectangle scale. -/
theorem bounded_firstHeight_norm
    (p : C(ℝ≥0, ℂ)) (hp0 : p 0 = 0) (hpH : ∀ t, 0 ≤ (p t).im)
    {B : ℝ} (hB : 0 < B) (T : ℝ≥0)
    (hcert : let σ := boundedFirstHeightTime p B T
      0 < σ ∧ (p σ).im = B / 4 ∧
        MapsTo (fun t => p (min t σ)) (Icc 0 T) (narrowStrip B)) :
    ∀ t ∈ Icc 0 (boundedFirstHeightTime p B T), ‖p t‖ < B / 2 := by
  obtain ⟨σ, htime, _, _, _, _, hpast⟩ :=
    bounded_certificate_gives_first_height p hp0 hpH hB T hcert
  have hσ : σ = boundedFirstHeightTime p B T := by
    have hle : σ ≤ T := by
      by_contra hn
      have hσmin := boundedFirstHeightTime_le p B T
      obtain ⟨_, hhit, _⟩ := hcert
      have hfirstle : firstHeightTime p (B / 4) ≤
          (boundedFirstHeightTime p B T : WithTop ℝ≥0) := by
        apply hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ boundedFirstHeightTime p B T from bot_le)
        change (p (boundedFirstHeightTime p B T)).im - B / 4 = 0
        rw [hhit, sub_self]
      rw [htime, WithTop.coe_le_coe] at hfirstle
      exact (not_le_of_gt (lt_of_not_ge hn)) (hfirstle.trans hσmin)
    apply WithTop.coe_injective
    rw [boundedFirstHeightTime_coe, htime, min_eq_left (WithTop.coe_le_coe.mpr hle)]
  intro t ht
  rw [← hσ] at ht
  exact mem_ball_zero_iff.mp
    (GuideSplice.closedInitialRectangle_subset_smallBall hB (hpast (mem_image_of_mem p ht)))

/-- Conformal localization controls a stopped containment failure whenever
the past remains below its parameter-radius threshold. -/
theorem unit_guide_localization
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ b C c L₀ : ℝ, 0 < b ∧ 0 < C ∧ 0 < c ∧ 1 < L₀ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
    ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
      DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
      ContinuousOn Fbar closedHalfPlane →
      (∀ z ∈ upperHalfPlane, Fbar z = (F z : OnePoint ℂ)) →
    ∀ (a : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (S : ℝ), 0 < S → ContinuousOn η (Icc 0 S) →
      η 0 = 0 → ‖η S‖ = 1 → (∀ t ∈ Icc 0 S, 0 ≤ (η t).im) →
      (∀ t ∈ Icc 0 S, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-a‖ ≤ r) →
    ∀ (L : ℝ), L₀ ≤ L → ∀ (σ : Ω → ℝ≥0) (E : Set Ω),
      (∀ ω ∈ E, ∀ t ∈ Icc 0 (σ ω), ‖γ ω t‖ < L ^ b) →
      P (E \ stoppedImageEvent γ σ Fbar a (L * r)) ≤ ENNReal.ofReal (C * L ^ (-c)) := by
  obtain ⟨b, C, c, L₀, hb, hC, hc, hL₀, hloc⟩ :=
    sourceUniformConformalLocalization κ hκ hκ8
  refine ⟨b, C, c, L₀, hb, hC, hc, hL₀, ?_⟩
  intro Ω m P hP γ hSLE F Fbar hF hinj hbar hext a r hr η S hS hη hη0 hηS hH him L hL σ E hbound
  exact (measure_mono (stoppedImage_failure_subset_escape γ σ E Fbar a (L * r) (L ^ b) hbound)).trans
    (hloc Ω m P hP γ hSLE F Fbar hF hinj hbar hext a r hr η S hS hη hη0 hηS hH him L hL)

/-- Actual capacity scaling transports an escape event, including its
strict before-first-modulus condition. -/
theorem escape_under_scaling
    {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (Fbar : ℂ → OnePoint ℂ)
    (c : ℝ≥0) (hc : 0 < c) (A r : ℝ) (a : ℂ) :
    {ω | ∃ t : ℝ≥0, BeforeFirstModulus (γ ω) A t ∧
      Fbar (γ ω t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' ball a r} ⊆
    {ω | ∃ t : ℝ≥0, BeforeFirstModulus (sourceScaleTrace c (γ ω)) ((c : ℝ) * A) t ∧
      Fbar (sourceScaleTrace c (γ ω) t / (c : ℂ)) ∉
        (fun z : ℂ => (z : OnePoint ℂ)) '' ball a r} := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  rintro ω ⟨t, ht, hbad⟩
  refine ⟨t * c ^ 2, ?_, ?_⟩
  · intro u hu
    have hu' : sourceScaleTime c u < t := (div_lt_iff₀ hc2).mpr hu
    have hn : ‖sourceScaleTrace c (γ ω) u‖ = (c : ℝ) * ‖γ ω (sourceScaleTime c u)‖ := by
      simp only [sourceScaleTrace, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg c.coe_nonneg]
    rw [hn]
    exact mul_lt_mul_of_pos_left (ht _ hu') hc
  · simpa only [sourceScaleTrace, sourceScaleTime,
      mul_div_cancel_right₀ _ (ne_of_gt hc2), mul_div_cancel_left₀ _ hcC] using hbad

/-- The localization estimate with a guide ending at an arbitrary positive
parameter radius, derived by capacity scaling of ordinary SLE. -/
theorem localization_at_guide_radius
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ b C c L₀ : ℝ, 0 < b ∧ 0 < C ∧ 0 < c ∧ 1 < L₀ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
    ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
      DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
      ContinuousOn Fbar closedHalfPlane →
      (∀ z ∈ upperHalfPlane, Fbar z = (F z : OnePoint ℂ)) →
    ∀ (a : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (S b₀ : ℝ), 0 < S → 0 < b₀ → ContinuousOn η (Icc 0 S) →
      η 0 = 0 → ‖η S‖ = b₀ → (∀ t ∈ Icc 0 S, 0 ≤ (η t).im) →
      (∀ t ∈ Icc 0 S, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-a‖ ≤ r) →
    ∀ (L : ℝ), L₀ ≤ L →
      P {ω | ∃ t : ℝ≥0, BeforeFirstModulus (γ ω) (b₀ * L ^ b) t ∧
        Fbar (γ ω t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' ball a (L * r)} ≤
      ENNReal.ofReal (C * L ^ (-c)) := by
  obtain ⟨b, C, c, L₀, hb, hC, hc, hL₀, hloc⟩ :=
    sourceUniformConformalLocalization κ hκ hκ8
  refine ⟨b, C, c, L₀, hb, hC, hc, hL₀, ?_⟩
  intro Ω m P hP γ hSLE F Fbar hF hinj hbar hext a r hr η S b₀ hS hb₀ hη hη0 hηS hH him L hL
  let d : ℝ≥0 := ⟨b₀, hb₀.le⟩
  let k := d⁻¹
  have hk : 0 < k := inv_pos.mpr hb₀
  have hkR : 0 < (k : ℝ) := hk
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hkR.ne'
  have hkd : (k : ℝ) * b₀ = 1 := by
    change b₀⁻¹ * b₀ = 1
    exact inv_mul_cancel₀ hb₀.ne'
  let Fs := fun z : ℂ => F (z / (k : ℂ))
  let Fbars := fun z : ℂ => Fbar (z / (k : ℂ))
  let ηs := fun t : ℝ => (k : ℂ) * η t
  have hmap (z : ℂ) (hz : z ∈ upperHalfPlane) : z / (k : ℂ) ∈ upperHalfPlane := by
    change 0 < (z / (k : ℂ)).im
    rw [Complex.div_ofReal_im]
    exact div_pos hz hkR
  have hFs : DifferentiableOn ℂ Fs upperHalfPlane :=
    hF.comp (differentiable_id.div_const (k : ℂ)).differentiableOn hmap
  have hFsi : InjOn Fs upperHalfPlane := by
    intro z hz w hw he
    have hh := hinj (hmap z hz) (hmap w hw) he
    exact (div_left_inj' hkC).mp hh
  have hbars : ContinuousOn Fbars closedHalfPlane :=
    hbar.comp (continuous_id.div_const (k : ℂ)).continuousOn (by
      intro z hz
      change 0 ≤ (z / (k : ℂ)).im
      rw [Complex.div_ofReal_im]
      exact div_nonneg hz hkR.le)
  have hexts (z : ℂ) (hz : z ∈ upperHalfPlane) : Fbars z = (Fs z : OnePoint ℂ) :=
    hext _ (hmap z hz)
  have hηsc : ContinuousOn ηs (Icc 0 S) := continuousOn_const.mul hη
  have hηs0 : ηs 0 = 0 := by simp only [ηs, hη0, mul_zero]
  have hηsS : ‖ηs S‖ = 1 := by
    simpa only [ηs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg k.coe_nonneg, hηS] using hkd
  have hηsH (t : ℝ) (ht : t ∈ Icc 0 S) : 0 ≤ (ηs t).im := by
    change 0 ≤ ((k : ℂ) * η t).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg hkR.le (hH t ht)
  have hims (t : ℝ) (ht : t ∈ Icc 0 S) :
      ∃ w : ℂ, Fbars (ηs t) = (w : OnePoint ℂ) ∧ ‖w - a‖ ≤ r := by
    simpa only [Fbars, ηs, mul_div_cancel_left₀ _ hkC] using him t ht
  have hscaled := sourceCapacityScaling.2 κ hκ hκ8 γ hSLE k hk
  have hbound := hloc Ω m P hP (fun ω => sourceScaleTrace k (γ ω)) hscaled
    Fs Fbars hFs hFsi hbars hexts a r hr ηs S hS hηsc hηs0 hηsS hηsH hims L hL
  have hsub := escape_under_scaling γ Fbar k hk (b₀ * L ^ b) (L * r) a
  have hfactor : (k : ℝ) * (b₀ * L ^ b) = L ^ b := by rw [← mul_assoc, hkd, one_mul]
  rw [hfactor] at hsub
  exact (measure_mono hsub).trans hbound

/-- The precise early-passage estimate: the bounded narrow first-height
past fails physical containment with probability at most the localization
power tail. -/
theorem bounded_firstHeight_localization
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ b C c L₀ : ℝ, 0 < b ∧ 0 < C ∧ 0 < c ∧ 1 < L₀ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
      (∀ ω, Continuous (γ ω)) → (∀ ω, γ ω 0 = 0) → (∀ ω t, 0 ≤ (γ ω t).im) →
    ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
      DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
      ContinuousOn Fbar closedHalfPlane →
      (∀ z ∈ upperHalfPlane, Fbar z = (F z : OnePoint ℂ)) →
    ∀ (a : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (S b₀ : ℝ), 0 < S → 0 < b₀ → ContinuousOn η (Icc 0 S) →
      η 0 = 0 → ‖η S‖ = b₀ → (∀ t ∈ Icc 0 S, 0 ≤ (η t).im) →
      (∀ t ∈ Icc 0 S, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-a‖ ≤ r) →
    ∀ (L : ℝ), L₀ ≤ L → ∀ (B : ℝ), 0 < B → B / 2 ≤ b₀ * L ^ b → ∀ T : ℝ≥0,
      let σ := fun ω => boundedFirstHeightTime (γ ω) B T
      P (stoppedNarrowCertificate γ σ B T \ stoppedImageEvent γ σ Fbar a (L * r)) ≤
        ENNReal.ofReal (C * L ^ (-c)) := by
  obtain ⟨b, C, c, L₀, hb, hC, hc, hL₀, hloc⟩ := localization_at_guide_radius κ hκ hκ8
  refine ⟨b, C, c, L₀, hb, hC, hc, hL₀, ?_⟩
  intro Ω m P hP γ hSLE hγc hγ0 hγH F Fbar hF hinj hbar hext a r hr η S b₀ hS hb₀ hη hη0 hηS hH him L hL B hB hBL T
  let σ := fun ω => boundedFirstHeightTime (γ ω) B T
  have hnorm : ∀ ω ∈ stoppedNarrowCertificate γ σ B T,
      ∀ t ∈ Icc 0 (σ ω), ‖γ ω t‖ < b₀ * L ^ b := by
    intro ω hω t ht
    exact (bounded_firstHeight_norm ⟨γ ω, hγc ω⟩ (hγ0 ω) (hγH ω) hB T hω t ht).trans_le hBL
  exact (measure_mono (stoppedImage_failure_subset_escape γ σ
    (stoppedNarrowCertificate γ σ B T) Fbar a (L * r) (b₀ * L ^ b) hnorm)).trans
      (hloc Ω P γ hSLE F Fbar hF hinj hbar hext a r hr η S b₀ hS hb₀ hη hη0 hηS hH him L hL)

end SLEExactGauge.EarlyPassageLocalization

end

end OAI
