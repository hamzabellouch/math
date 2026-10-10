import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem358

/-- Joint measurability is preserved by integrating between measurable endpoints. -/
theorem stronglyMeasurable_intervalIntegral_endpoints
    {X : Type*} [MeasurableSpace X] {f : X → ℝ → ℝ} {a b : X → ℝ}
    (hf : Measurable (Function.uncurry f)) (ha : Measurable a) (hb : Measurable b) :
    StronglyMeasurable (fun x => ∫ t in a x..b x, f x t) := by
  let S : Set (X × ℝ) := {p | a p.1 < p.2 ∧ p.2 ≤ b p.1}
  let T : Set (X × ℝ) := {p | b p.1 < p.2 ∧ p.2 ≤ a p.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))
  have hT : MeasurableSet T :=
    (measurableSet_lt (hb.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (ha.comp measurable_fst))
  have hleft : StronglyMeasurable (fun x => ∫ t : ℝ,
      S.indicator (Function.uncurry f) (x, t)) :=
    StronglyMeasurable.integral_prod_right (f := fun x t =>
      S.indicator (Function.uncurry f) (x, t)) (by
        convert (hf.indicator hS).stronglyMeasurable using 1
        funext p
        rcases p with ⟨x, t⟩
        rfl)
  have hright : StronglyMeasurable (fun x => ∫ t : ℝ,
      T.indicator (Function.uncurry f) (x, t)) :=
    StronglyMeasurable.integral_prod_right (f := fun x t =>
      T.indicator (Function.uncurry f) (x, t)) (by
        convert (hf.indicator hT).stronglyMeasurable using 1
        funext p
        rcases p with ⟨x, t⟩
        rfl)
  convert hleft.sub hright using 1
  ext x
  change (∫ t in a x..b x, f x t) =
    (∫ t, (Set.Ioc (a x) (b x)).indicator (f x) t) -
      (∫ t, (Set.Ioc (b x) (a x)).indicator (f x) t)
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rfl

/-- Differentiate a moving one-dimensional boundary, then integrate over the
transverse variables. Continuity is required only at the unperturbed boundary;
the integrand may be discontinuous away from that boundary. -/
theorem hasDerivAt_integral_moving_boundary
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ → ℝ} {b B : X → ℝ}
    (hmeas : ∀ h : ℝ, AEStronglyMeasurable
      (fun x => ∫ t in (0 : ℝ)..h * b x, f x t) μ)
    (htrace : AEStronglyMeasurable (fun x => f x 0 * b x) μ)
    (hslice : ∀ᵐ x ∂μ, StronglyMeasurableAtFilter (f x) (nhds 0))
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (f x) 0)
    (hbound : ∀ᵐ x ∂μ, ∀ t : ℝ, ‖f x t‖ ≤ B x)
    (hdom : Integrable (fun x => |b x| * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t in (0 : ℝ)..h * b x, f x t) ∂μ)
      (∫ x, f x 0 * b x ∂μ) 0 := by
  let F : ℝ → X → ℝ := fun h x => ∫ t in (0 : ℝ)..h * b x, f x t
  let D : X → ℝ →L[ℝ] ℝ := fun x =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (f x 0 * b x)
  have hDmeas : AEStronglyMeasurable D μ :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp_aestronglyMeasurable htrace
  have hdiff : ∀ᵐ x ∂μ, HasFDerivAt (fun h => F h x) (D x) 0 := by
    filter_upwards [hslice, hcont] with x hx hc
    have hf := intervalIntegral.integral_hasDerivAt_right
      (IntervalIntegrable.refl (f := f x) (a := (0 : ℝ))) hx hc
    have hmul := (hasDerivAt_id (0 : ℝ)).mul_const (b x)
    have hf' : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, f x t)
        (f x 0) ((fun h : ℝ => id h * b x) 0) := by
      simpa using hf
    have hd : HasDerivAt (fun h => F h x) (f x 0 * b x) 0 := by
      simpa [F, Function.comp_def] using hf'.comp 0 hmul
    exact hd.hasFDerivAt
  have hbase : Integrable (F 0) μ := by
    simp [F]
  have hlip : ∀ᵐ x ∂μ, ∀ h ∈ (Set.univ : Set ℝ),
      ‖F h x - F 0 x‖ ≤ (|b x| * B x) * ‖h - 0‖ := by
    filter_upwards [hbound] with x hx
    intro h _
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := h * b x) (fun t _ => hx t)
    simpa [F, abs_mul, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hi
  obtain ⟨hDint, hD⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F := F) (F' := D) (s := Set.univ) (x₀ := (0 : ℝ))
    (bound := fun x => |b x| * B x) Filter.univ_mem
    (fun h _ => hmeas h) hbase hDmeas hlip hdom hdiff
  have hd := hD.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hDint] at hd
  simpa [D, F] using hd

/-- A moving-boundary derivative with all measurability discharged from a jointly
measurable integrand and a measurable boundary velocity. -/
theorem hasDerivAt_integral_moving_boundary_of_measurable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ → ℝ} {b B : X → ℝ}
    (hf : Measurable (Function.uncurry f)) (hb : Measurable b)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (f x) 0)
    (hbound : ∀ᵐ x ∂μ, ∀ t : ℝ, ‖f x t‖ ≤ B x)
    (hdom : Integrable (fun x => |b x| * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t in (0 : ℝ)..h * b x, f x t) ∂μ)
      (∫ x, f x 0 * b x ∂μ) 0 := by
  apply hasDerivAt_integral_moving_boundary _ _ _ hcont hbound hdom
  · intro h
    exact (stronglyMeasurable_intervalIntegral_endpoints hf measurable_const
      (measurable_const.mul hb)).aestronglyMeasurable
  · exact ((hf.comp (measurable_id.prodMk measurable_const)).mul hb).aestronglyMeasurable
  · exact Eventually.of_forall fun x =>
      (hf.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.stronglyMeasurableAtFilter

/-- A moving-boundary derivative remains valid for a changing integrand. The
scaled pointwise limit is exactly what remains after removing the principal
moving halfspace in a telescoping product of cell indicators. -/
theorem hasDerivAt_integral_moving_boundary_varying
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {b B : X → ℝ} {trace : X → ℝ}
    (hf : ∀ h, Measurable (Function.uncurry (f h))) (hb : Measurable b)
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (h * u)) (nhds 0) (nhds (trace x)))
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => |b x| * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t in (0 : ℝ)..h * b x, f h x t) ∂μ)
      (∫ x, b x * trace x ∂μ) 0 := by
  let G : ℝ → X → ℝ := fun h x => ∫ u in (0 : ℝ)..b x, f h x (h * u)
  have hGmeas : ∀ h, StronglyMeasurable (G h) := by
    intro h
    apply stronglyMeasurable_intervalIntegral_endpoints _ measurable_const hb
    exact (hf h).comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hGbound : ∀ h, ∀ᵐ x ∂μ, ‖G h x‖ ≤ |b x| * B x := by
    intro h
    filter_upwards [hbound] with x hx
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := b x) (fun u _ => hx h (h * u))
    simpa [G, mul_comm] using hi
  have hGlim : ∀ᵐ x ∂μ, Tendsto (fun h => G h x) (nhds 0)
      (nhds (b x * trace x)) := by
    filter_upwards [hlim, hbound] with x hx hxbound
    have hi := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := (0 : ℝ)) (b := b x) (μ := volume) (l := nhds (0 : ℝ))
      (F := fun h u => f h x (h * u)) (f := fun _ => trace x)
      (fun _ => B x)
      (Eventually.of_forall fun h =>
        ((hf h).comp (measurable_const.prodMk
          (measurable_const.mul measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun h => Eventually.of_forall fun u _ => hxbound h (h * u))
      intervalIntegrable_const
      (Eventually.of_forall fun u _ => hx u)
    simpa [G] using hi
  have hHlim : Tendsto (fun h => ∫ x, G h x ∂μ) (nhds 0)
      (nhds (∫ x, b x * trace x ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence (fun x => |b x| * B x)
      (Eventually.of_forall fun h => (hGmeas h).aestronglyMeasurable)
      (Eventually.of_forall hGbound) hdom hGlim
  have hscale : ∀ h : ℝ,
      (∫ x, (∫ t in (0 : ℝ)..h * b x, f h x t) ∂μ) =
        h * ∫ x, G h x ∂μ := by
    intro h
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simpa only [G, smul_eq_mul, mul_zero] using
        (intervalIntegral.smul_integral_comp_mul_left (f h x) (a := (0 : ℝ))
          (b := b x) h).symm
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply (hHlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  simp [hscale, hh0, smul_eq_mul]

/-- A varying boundary velocity is allowed as well. In moving-plane coordinates,
this covers the denominator introduced when the normal direction is perturbed. -/
theorem hasDerivAt_integral_moving_boundary_varying_speed
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (h * speed h x * u)) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h : ℝ, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t in (0 : ℝ)..h * speed h x, f h x t) ∂μ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  let G : ℝ → X → ℝ → ℝ := fun h x t => speed h x * f h x (speed h x * t)
  have hGmeas : ∀ h, Measurable (Function.uncurry (G h)) := by
    intro h
    exact ((hspeed h).comp measurable_fst).mul
      ((hf h).comp (measurable_fst.prodMk
        (((hspeed h).comp measurable_fst).mul measurable_snd)))
  have hGlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => G h x (h * u)) (nhds 0)
        (nhds (slope x * trace x)) := by
    filter_upwards [hspeedlim, hlim] with x hx hy
    intro u
    simpa [G, mul_assoc, mul_comm, mul_left_comm] using hx.mul (hy u)
  have hGbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖G h x t‖ ≤ A x * B x := by
    filter_upwards [hspeedbound, hbound] with x hx hy
    intro h t
    have hB : 0 ≤ B x := (norm_nonneg _).trans (hy 0 0)
    calc
      ‖G h x t‖ = |speed h x| * ‖f h x (speed h x * t)‖ := by
        simp [G, norm_mul, Real.norm_eq_abs]
      _ ≤ A x * B x := mul_le_mul (hx h) (hy h (speed h x * t))
        (norm_nonneg _) ((abs_nonneg _).trans (hx h))
  have hg := hasDerivAt_integral_moving_boundary_varying
    (f := G) (b := fun _ => (1 : ℝ)) (B := fun x => A x * B x)
    hGmeas measurable_const hGlim hGbound (by simpa using hdom)
  simp only [mul_one, one_mul] at hg
  convert hg using 1
  funext h
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∫ t in (0 : ℝ)..h * speed h x, f h x t) =
      (∫ t in (0 : ℝ)..h, G h x t)
    rw [show (∫ t in (0 : ℝ)..h, G h x t) =
      speed h x * ∫ t in (0 : ℝ)..h, f h x (speed h x * t) by
        exact intervalIntegral.integral_const_mul _ _]
    simpa only [smul_eq_mul, mul_zero, mul_comm] using
      (intervalIntegral.smul_integral_comp_mul_left (f h x)
        (a := (0 : ℝ)) (b := h) (speed h x)).symm

end Problem358

namespace Problem358

/-- The signed change of a threshold halfline is exactly its boundary strip. -/
theorem integral_threshold_difference (f : ℝ → ℝ) (c : ℝ) :
    (∫ t : ℝ, f t * ((if c ≤ t then (1 : ℝ) else 0) -
      (if 0 ≤ t then (1 : ℝ) else 0))) = ∫ t in c..0, f t := by
  classical
  by_cases hc : c ≤ 0
  · have hid : (fun t : ℝ => f t * ((if c ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) = (Set.Ico c 0).indicator f := by
      funext t
      simp only [Set.indicator, Set.mem_Ico]
      split_ifs <;> simp_all <;> linarith
    rw [hid, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      intervalIntegral.integral_of_le hc]
  · have hc' : 0 ≤ c := le_of_lt (lt_of_not_ge hc)
    have hid : (fun t : ℝ => f t * ((if c ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) =
        fun t => -((Set.Ico 0 c).indicator f t) := by
      funext t
      simp only [Set.indicator, Set.mem_Ico]
      split_ifs <;> simp_all <;> linarith
    rw [hid, integral_neg, integral_indicator measurableSet_Ico,
      integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_ge hc']

/-- The derivative of one varying halfspace factor, with all other varying
factors included in `f`. This is stated as an iterated integral so that an
orthogonal-coordinate/Fubini argument can apply it directly. -/
theorem hasDerivAt_integral_halfspace_difference
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (-(h * speed h x * u))) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h : ℝ, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t : ℝ,
      f h x t * ((if -(h * speed h x) ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) ∂μ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  have hg := hasDerivAt_integral_moving_boundary_varying_speed
    (f := fun h x t => f h x (-t)) (speed := speed)
    (A := A) (B := B) (slope := slope) (trace := trace)
    (fun h => (hf h).comp (measurable_fst.prodMk measurable_snd.neg))
    hspeed hspeedlim hlim hspeedbound
    (hbound.mono fun x hx h t => hx h (-t)) hdom
  convert hg using 1
  funext h
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [integral_threshold_difference, intervalIntegral.integral_comp_neg]
    simp

/-- Local-in-parameter version of the halfspace derivative. In particular,
velocity denominators need only stay away from zero near the base configuration. -/
theorem hasDerivAt_integral_halfspace_difference_local
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    {s : Set ℝ} (hs : s ∈ nhds 0)
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (-(h * speed h x * u))) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h ∈ s, ∀ t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t : ℝ,
      f h x t * ((if -(h * speed h x) ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) ∂μ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  classical
  let ff : ℝ → X → ℝ → ℝ := fun h x t => if h ∈ s then f h x t else 0
  let vv : ℝ → X → ℝ := fun h x => if h ∈ s then speed h x else 0
  have hzero : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  have hff : ∀ h, Measurable (Function.uncurry (ff h)) := by
    intro h
    by_cases hh : h ∈ s
    · simpa [ff, hh, Function.uncurry] using hf h
    · convert (measurable_const : Measurable (fun _ : X × ℝ => (0 : ℝ))) using 1
      funext p
      rcases p with ⟨x, t⟩
      simp [ff, hh]
  have hvv : ∀ h, Measurable (vv h) := by
    intro h
    by_cases hh : h ∈ s
    · simpa [vv, hh] using hspeed h
    · simp [vv, hh]
  have hvlim : ∀ᵐ x ∂μ, Tendsto (fun h => vv h x) (nhds 0) (nhds (slope x)) := by
    filter_upwards [hspeedlim] with x hx
    apply hx.congr'
    filter_upwards [hs] with h hh
    simp [vv, hh]
  have hflim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => ff h x (-(h * vv h x * u))) (nhds 0) (nhds (trace x)) := by
    filter_upwards [hlim] with x hx
    intro u
    apply (hx u).congr'
    filter_upwards [hs] with h hh
    simp [ff, vv, hh]
  have hvbound : ∀ᵐ x ∂μ, ∀ h : ℝ, |vv h x| ≤ A x := by
    filter_upwards [hspeedbound] with x hx
    have hA : 0 ≤ A x := (abs_nonneg _).trans (hx 0 hzero)
    intro h
    by_cases hh : h ∈ s
    · simpa [vv, hh] using hx h hh
    · simpa [vv, hh] using hA
  have hfbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖ff h x t‖ ≤ B x := by
    filter_upwards [hbound] with x hx
    have hB : 0 ≤ B x := (norm_nonneg _).trans (hx 0 hzero 0)
    intro h t
    by_cases hh : h ∈ s
    · simpa [ff, hh] using hx h hh t
    · simpa [ff, hh] using hB
  have hd := hasDerivAt_integral_halfspace_difference hff hvv hvlim hflim hvbound hfbound hdom
  apply hd.congr_of_eventuallyEq
  filter_upwards [hs] with h hh
  simp [ff, vv, hh]

/-- Multiplication by the signed difference of two threshold indicators
preserves ambient integrability. -/
theorem integrable_threshold_difference
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X × ℝ → ℝ} {c : X → ℝ}
    (hf : Integrable f (μ.prod volume)) (hc : Measurable c) :
    Integrable (fun p : X × ℝ => f p *
      ((if c p.1 ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0))) (μ.prod volume) := by
  have hfirst : Measurable (fun p : X × ℝ =>
      if c p.1 ≤ p.2 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (hc.comp measurable_fst) measurable_snd)
      measurable_const measurable_const
  have hsecond : Measurable (fun p : X × ℝ =>
      if 0 ≤ p.2 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const measurable_snd)
      measurable_const measurable_const
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul
    (hfirst.sub hsecond).aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    have hcut : ‖(if c p.1 ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0)‖ ≤ 1 := by
      split_ifs <;> norm_num
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hcut (norm_nonneg _)).trans_eq (mul_one _)

/-- Product-measure version of the local moving-face derivative. Ambient
integrability is enough to discharge the Fubini step, while slice domination
controls the derivative independently of the parameter. -/
theorem hasDerivAt_prod_integral_halfspace_difference_local
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    {s : Set ℝ} (hs : s ∈ nhds 0)
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (-(h * speed h x * u))) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h ∈ s, ∀ t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ)
    (hInt : ∀ᶠ h in nhds 0, Integrable (Function.uncurry (f h)) (μ.prod volume)) :
    HasDerivAt (fun h : ℝ => ∫ p : X × ℝ,
      f h p.1 p.2 * ((if -(h * speed h p.1) ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0)) ∂μ.prod volume)
      (∫ x, slope x * trace x ∂μ) 0 := by
  have hd := hasDerivAt_integral_halfspace_difference_local hs hf hspeed
    hspeedlim hlim hspeedbound hbound hdom
  apply hd.congr_of_eventuallyEq
  filter_upwards [hInt] with h hh
  exact integral_prod _ (integrable_threshold_difference hh
    (measurable_const.mul (hspeed h)).neg)

end Problem358

end

end OAI
