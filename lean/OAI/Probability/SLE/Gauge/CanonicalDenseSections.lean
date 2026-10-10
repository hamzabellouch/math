import OAI.Probability.SLE.Loewner.CanonicalRadiusKernel
import OAI.Probability.SLE.Gauge.ConformalDenseExperiment
import OAI.Probability.SLE.Gauge.RandomPassageBounds

namespace OAI

/-! Measurable canonical sections for the proved conformal dense experiment.
The probability estimate is transported from the actual SLE theorem; the
canonical path and stopping kernels introduce no further stochastic input. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open FrontSuccessMeasurability

local instance denseSectionDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance denseSectionDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance denseSectionPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance denseSectionPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma measurable_stoppedAtPath
    {X : Type*} [MeasurableSpace X]
    (f : X → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (τ : X → WithTop ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun x => stoppedAtPath (f x) (τ x)) := by
  apply source_path_measurable
  intro t
  have hm : Measurable (fun x => f x
      ((min (τ x) (t : WithTop ℝ≥0)).untopD (Classical.arbitrary ℝ≥0))) :=
    continuous_eval.measurable.comp
      (hf.prodMk ((hτ.min measurable_const).untopD (Classical.arbitrary ℝ≥0)))
  simpa only [stoppedAtPath_apply, WithTop.untopA] using hm

lemma measurable_wholeSausageCharge_closedBall
    {X : Type*} [MeasurableSpace X]
    (κ v : ℝ) (f : X → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (a : X → ℂ) (ha : Measurable a) (r : X → ℝ) (hr : Measurable r) :
    Measurable (fun x => wholeSausageCharge κ (f x) v (closedBall (a x) (r x))) := by
  let I : X × ℂ → ℝ≥0∞ := fun p =>
    if p.2 ∈ closedBall (a p.1) (r p.1) ∩ wholeSausageSet (f p.1) v then 1 else 0
  have hball : MeasurableSet {p : X × ℂ | p.2 ∈ closedBall (a p.1) (r p.1)} :=
    measurableSet_le (measurable_snd.dist (ha.comp measurable_fst)) (hr.comp measurable_fst)
  have hsausage : MeasurableSet {p : X × ℂ | p.2 ∈ wholeSausageSet (f p.1) v} :=
    (wholeSausage_joint_open v).measurableSet.preimage
      ((hf.comp measurable_fst).prodMk measurable_snd)
  have hI : Measurable I := Measurable.ite (hball.inter hsausage)
    measurable_const measurable_const
  have he (x : X) : wholeSausageCharge κ (f x) v (closedBall (a x) (r x)) =
      ENNReal.ofReal (v ^ (-codimension κ)) * ∫⁻ z, I (x, z) ∂volume := by
    unfold wholeSausageCharge
    congr 1
    have hIeq : (fun z => I (x, z)) =
        (closedBall (a x) (r x) ∩ wholeSausageSet (f x) v).indicator (fun _ => 1) := by
      funext z
      by_cases hz : z ∈ closedBall (a x) (r x) ∩ wholeSausageSet (f x) v
      · simp only [I, ite_eq_left hz, indicator_of_mem hz]
      · simp only [I, ite_eq_right hz, indicator_of_notMem hz]
    rw [hIeq]
    exact (lintegral_indicator_one (μ := volume) (isClosed_closedBall.measurableSet.inter
      (wholeSausageSet_isOpen (f x) v).measurableSet)).symm
  simp_rw [he]
  exact measurable_const.mul (hI.lintegral_prod_right' (ν := volume))

def canonicalDenseEvent (κ : ℝ) (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
    (Fb : C(closedHalfPlane, ℂ)) (u : ℝ) (w : ℂ) (b r : ℝ)
    (m : ℕ) (v : ℝ) (a : ℂ) : Set C(ℝ≥0, ℝ) :=
  {p | ENNReal.ofReal (b * r ^ dimension κ * (m : ℝ) ^ codimension κ) ≤
    stoppedWholeSausageCharge κ (finiteBoundaryPath Fb (Φ p))
      (canonicalRadiusLevel κ (u, w, p)) v (closedBall a r)}

/-- All geometric marked parameters may be random. In particular this
applies to the product of the stopped past with a fresh driver path. -/
lemma measurableSet_canonicalDenseEvent_random
    {X : Type*} [MeasurableSpace X]
    (κ b v : ℝ) (m : ℕ) (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (hΦ : Measurable Φ)
    (Fb : X → C(closedHalfPlane, ℂ)) (hFb : Measurable Fb)
    (u : X → ℝ) (hu : Measurable u) (w : X → ℂ) (hw : Measurable w)
    (r : X → ℝ) (hr : Measurable r) (a : X → ℂ) (ha : Measurable a)
    (Y : X → C(ℝ≥0, ℝ)) (hY : Measurable Y) :
    MeasurableSet {x | Y x ∈ canonicalDenseEvent κ Φ (Fb x) (u x) (w x)
      b (r x) m v (a x)} := by
  have hpath : Measurable (fun x => finiteBoundaryPath (Fb x) (Φ (Y x))) :=
    (measurable_random_finiteBoundaryPath Fb hFb).comp
      (measurable_id.prodMk (hΦ.comp hY))
  have hstop := measurable_stoppedAtPath _ hpath _
    (measurable_canonicalRadiusLevel_random_state κ hY hu hw)
  have hmass := measurable_wholeSausageCharge_closedBall κ v _ hstop a ha r hr
  have hthresh : Measurable (fun x => ENNReal.ofReal
      (b * r x ^ dimension κ * (m : ℝ) ^ codimension κ)) := by fun_prop
  exact measurableSet_le hthresh hmass

lemma measurableSet_canonicalDenseEvent
    (κ b r v : ℝ) (m : ℕ) (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (hΦ : Measurable Φ)
    (Fb : C(closedHalfPlane, ℂ)) (u : ℝ) (w a : ℂ) :
    MeasurableSet (canonicalDenseEvent κ Φ Fb u w b r m v a) := by
  exact measurableSet_canonicalDenseEvent_random κ b v m Φ hΦ
    (fun _ => Fb) measurable_const (fun _ => u) measurable_const
    (fun _ => w) measurable_const (fun _ => r) measurable_const
    (fun _ => a) measurable_const id measurable_id

lemma measurableSet_canonicalDenseEvent_product
    {X : Type*} [MeasurableSpace X]
    (κ b v : ℝ) (m : ℕ) (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (hΦ : Measurable Φ)
    (Fb : X → C(closedHalfPlane, ℂ)) (hFb : Measurable Fb)
    (u : X → ℝ) (hu : Measurable u) (w : X → ℂ) (hw : Measurable w)
    (r : X → ℝ) (hr : Measurable r) (a : X → ℂ) (ha : Measurable a) :
    MeasurableSet {x : X × C(ℝ≥0, ℝ) |
      x.2 ∈ canonicalDenseEvent κ Φ (Fb x.1) (u x.1) (w x.1)
        b (r x.1) m v (a x.1)} :=
  measurableSet_canonicalDenseEvent_random κ b v m Φ hΦ
    _ (hFb.comp measurable_fst) _ (hu.comp measurable_fst)
    _ (hw.comp measurable_fst) _ (hr.comp measurable_fst)
    _ (ha.comp measurable_fst) _ measurable_snd

lemma map_withDensity_comp
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (d : Y → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity (fun x => d (f x))).map f = (μ.map f).withDensity d := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hf hS, withDensity_apply _ (hf hS), withDensity_apply _ hS,
    setLIntegral_map hS hd hf]

/-- The canonical density is exactly the pushforward of the original
finite centered law, simultaneously for any chosen nonnegative level. -/
theorem canonical_finiteCenteredLaw_map
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂μ, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (w : ℂ) :
    (finiteCenteredLaw μ κ B γ G w u).map (sourceDriverPath B hc) =
      (μ.map (sourceDriverPath B hc)).withDensity
        (fun p => canonicalFiniteDensity κ (u, w, p)) := by
  have hbp := source_path_measurable (sourceDriverPath B hc) hm
  have hd : Measurable (fun p => canonicalFiniteDensity κ (u, w, p)) :=
    (canonicalFiniteDensity_measurable κ).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have he : finiteCenteredLaw μ κ B γ G w u =
      μ.withDensity (fun ω => canonicalFiniteDensity κ (u, w, sourceDriverPath B hc ω)) := by
    unfold finiteCenteredLaw
    apply withDensity_congr_ae
    filter_upwards [hw] with ω hω
    exact (canonicalFiniteDensity_eq κ (sourceDriverPath B hc ω) hω u hu w).symm
  rw [he, map_withDensity_comp μ _ hbp _ hd]

namespace Serpentine
open Target

/-- The conformal dense-experiment theorem on canonical driver space.
The constants are those of the proved actual SLE theorem, with half the
height margin reserved to use the finite boundary chart on the interior. -/
theorem uniform_canonical_conformal_dense_sections
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (hΦ : Measurable Φ)
    (hΦγ : ∀ᵐ ω ∂μ, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω)
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ h b C : ℝ, 0 < h ∧ h ≤ s / 2 ∧ 0 < b ∧ 0 < C ∧
      ∃ δ : ℕ → ℝ, (∀ m, 0 < m → 0 < δ m) ∧
      ∀ (f : ℂ → ℂ) (Fb : C(closedHalfPlane, ℂ)) (w : ℂ),
        DifferentiableOn ℂ f upperHalfPlane → InjOn f upperHalfPlane →
        (∀ z : closedHalfPlane, (z : ℂ) ∈ upperHalfPlane → Fb z = f z) →
        ‖w‖ = 1 → s ≤ w.im → deriv f w ≠ 0 →
        ∀ m : ℕ, 0 < m → ∀ v : ℝ, 0 < v →
          v < δ m * (2 * w.im * ‖deriv f w‖) →
          ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) ≤
            ((μ.map (sourceDriverPath B hc)).withDensity
              (fun p => canonicalFiniteDensity κ (experimentRadiusLevel h, w, p)))
              (canonicalDenseEvent κ Φ Fb (experimentRadiusLevel h) w b
                (2 * w.im * ‖deriv f w‖) m v (f w)) := by
  have hs2 : 0 < s / 2 := by positivity
  have hs21 : s / 2 ≤ 1 := by linarith
  obtain ⟨h, b, C, hh, hhs, hb, hC, δ, hδ, hmass⟩ :=
    uniform_conformal_dense_stopped_mass μ κ hκ hκ8 B hB hBm hc hB0 γ G F hw
      hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW ε hε hεsmall hs2 hs21
  refine ⟨h, b, C, hh, hhs, hb, hC, δ, hδ, ?_⟩
  intro f Fb w hf hfi hFb hwn hwy hne m hm v hv hvcut
  let bp := sourceDriverPath B hc
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  let η : Ω → ℝ≥0 → ℂ := fun ω => finiteBoundaryPath Fb (gp ω)
  have hη : ∀ ω, Continuous (η ω) := fun ω => (finiteBoundaryPath Fb (gp ω)).continuous
  have hηeq (ω : Ω) (t : ℝ≥0) (ht : γ ω t ∈ closedBall w h) : η ω t = f (γ ω t) := by
    have hib : w.im - (γ ω t).im ≤ h := by
      calc
        _ = (w - γ ω t).im := rfl
        _ ≤ ‖w - γ ω t‖ := Complex.im_le_norm _
        _ = dist (γ ω t) w := by rw [dist_eq_norm, norm_sub_rev]
        _ ≤ h := ht
    have hpos : γ ω t ∈ upperHalfPlane := by change 0 < (γ ω t).im; linarith
    have hclosed : ClosedPathProperty (gp ω) := by
      intro t
      exact (hw ω).2.2.1 t
    change finiteBoundaryPath Fb (gp ω) t = _
    rw [finiteBoundaryPath_apply Fb (gp ω) hclosed t]
    exact hFb _ hpos
  let ρ : Ω → WithTop ℝ≥0 := fun ω => canonicalRadiusLevel κ (experimentRadiusLevel h, w, bp ω)
  have hu : 0 ≤ experimentRadiusLevel h := experimentRadiusLevel_nonneg hh (by linarith)
  have hρ : ∀ᵐ ω ∂μ, ρ ω = radiusLevelTime (γ ω) (G ω) w (experimentRadiusLevel h) :=
    Eventually.of_forall fun ω => canonicalRadiusLevel_eq κ (bp ω) (hw ω) _ hu w
  have hp := hmass f w hf hfi hwn (by linarith) hne η hη hηeq ρ hρ m hm v hv hvcut
  let E := canonicalDenseEvent κ Φ Fb (experimentRadiusLevel h) w b
    (2 * w.im * ‖deriv f w‖) m v (f w)
  have hE : MeasurableSet E := measurableSet_canonicalDenseEvent _ _ _ _ _ Φ hΦ Fb _ _ _
  have hmB : ∀ t, Measurable (B t) := fun t => hBm.comp (measurable_const.prodMk measurable_id)
  rw [← canonical_finiteCenteredLaw_map μ κ B hmB hc γ G F
    (Eventually.of_forall hw) _ hu w, Measure.map_apply (source_path_measurable bp hmB) hE]
  apply hp.trans_eq
  apply measure_congr
  apply (withDensity_absolutelyContinuous μ _).ae_le
  filter_upwards [hΦγ] with ω hω
  apply propext
  change (ENNReal.ofReal _ ≤ stoppedWholeSausageCharge κ (sourceTracePath η hη ω) (ρ ω) v _) ↔
    (ENNReal.ofReal _ ≤ stoppedWholeSausageCharge κ (finiteBoundaryPath Fb (Φ (bp ω))) (ρ ω) v _)
  rw [hω]
  rfl

end Serpentine
end SLEExactGauge

end

end OAI
