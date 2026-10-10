import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedProductionLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.WindowCollisionMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicJointBudgetLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # Actual gain limits with bounded spatial mass and a fixed elastic window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def clippedFiniteGain (N K R : ℝ) (f : X × Velocity → ℝ) : X × Velocity → ℝ :=
  windowCollisionMarginal R (fun z => collisionMassClip K f z*massRegularizedPostRate N f z)

def clippedPhysicalGain (K R : ℝ) (f : X × Velocity → ℝ) : X × Velocity → ℝ :=
  windowCollisionMarginal R (fun z => collisionMassClip K f z*massNormalizedPostRate f z)

theorem clippedFiniteGain_measurable (N K R : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (clippedFiniteGain N K R f) :=
  windowCollisionMarginal_measurable R ((collisionMassClip_measurable K hfm).mul
    (massRegularizedPostRate_measurable N hfm))

theorem clippedPhysicalGain_measurable (K R : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (clippedPhysicalGain K R f) :=
  windowCollisionMarginal_measurable R ((collisionMassClip_measurable K hfm).mul
    (massNormalizedPostRate_measurable hfm))

theorem GlobalCollisionLimit.clipped_gain_limit {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (K : ℝ≥0) :
    Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)
      (fun n => clippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      (clippedPhysicalGain K R G.weakLimit.kineticProfile) ∧
    UniformIntegrable
      (fun n => clippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) := by
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let N (n : ℕ) : ℝ := (G.weakLimit.indices n:ℝ)+1
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hN n : 0 < N n := by dsimp [N]; positivity
  have hFi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hFb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hclip n z : |collisionMassClip K (F n) z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg
      (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hFn n (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hu := uniformIntegrable_of_varying_multiplier
    (massRegularizedPostRate_window_uniformIntegrable hFm hFn hFi hFb hN hR)
    (fun n => collisionMassClip_measurable K (hFm n)) K hclip
  have hw := (weak_clipped_collision_rates hFm G.weakLimit.kineticProfile_measurable
    hFn (fun _ => G.weakLimit.nonnegative _) hFi hFb hN (G.mass_strong T hT)
    (G.finite_rates T hT).1 (G.finite_rates T hT).2 K hR).2
  exact ⟨weak_windowCollisionMarginal
    (fun n => (collisionMassClip_measurable K (hFm n)).mul
      (massRegularizedPostRate_measurable (N n) (hFm n))) hu hw,
    windowCollisionMarginal_uniformIntegrable hR
      (fun n => (collisionMassClip_measurable K (hFm n)).mul
        (massRegularizedPostRate_measurable (N n) (hFm n))) hu⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The clipped positive gain lies below the actual finite gain -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X]

private theorem clip_mul_div_bounds {K ρ a : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (ha : 0 ≤ a) :
    0 ≤ massClip K ρ*(a/(1+ρ)) ∧ massClip K ρ*(a/(1+ρ)) ≤ a := by
  have hd : 0 < 1+ρ := by linarith
  refine ⟨mul_nonneg (massClip_bounds hK hρ).1 (div_nonneg ha hd.le),?_⟩
  rw [← mul_div_assoc,div_le_iff₀ hd]
  have h := mul_le_mul_of_nonneg_right (min_le_right K (1+ρ)) ha
  dsimp only [massClip]
  nlinarith only [h]

theorem regularizedPostRate_fiber_full_integrable {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    Integrable (fun q => regularizedPostRate N f (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea) := by
  let V : Set (Velocity × Sphere) := Metric.closedBall 0 N ×ˢ univ
  have hV : MeasurableSet V := Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ
  have hi : IntegrableOn (fun q => regularizedPostRate N f (collisionGrouping.symm (p,q))) V
      ((volume : Measure Velocity).prod sphereArea) := by
    simpa only [IntegrableOn,V,← fiberMeasure_eq_restrict] using post_fiber_integrable hN hfm hf p
  have he : V.indicator (fun q => regularizedPostRate N f (collisionGrouping.symm (p,q))) =
      (fun q => regularizedPostRate N f (collisionGrouping.symm (p,q))) := by
    funext q
    by_cases hq : q ∈ V
    · exact indicator_of_mem hq _
    · rw [indicator_of_notMem hq]
      symm
      apply regularizedPostRate_zero_of_partner hN.le
      change N < ‖q.1‖
      simpa only [V,mem_prod,mem_univ,and_true,Metric.mem_closedBall,dist_zero_right,not_le] using hq
  simpa only [he] using hi.integrable_indicator hV

theorem clippedFiniteGain_bounds {N K R : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ clippedFiniteGain N K R f p ∧ clippedFiniteGain N K R f p ≤ gain N f p := by
  have hb (z : (X × (Velocity × Velocity)) × Sphere) :
      0 ≤ (collisionWindow R).indicator
        (fun z => collisionMassClip K f z*massRegularizedPostRate N f z) z ∧
      (collisionWindow R).indicator
        (fun z => collisionMassClip K f z*massRegularizedPostRate N f z) z ≤ regularizedPostRate N f z := by
    have hρ : 0 ≤ fiberMass volume f z.1.1 := integral_nonneg (fun v => hf (z.1.1,v))
    have ha : 0 ≤ regularizedPostRate N f z := (regularizedPreRate_bounds hN hf _).1
    by_cases hz : z ∈ collisionWindow R
    · rw [indicator_of_mem hz]
      exact clip_mul_div_bounds hK hρ ha
    · rw [indicator_of_notMem hz]
      exact ⟨le_rfl,ha⟩
  have hi := regularizedPostRate_fiber_full_integrable hN hfm hf p
  have hm : Measurable (fun q : Velocity × Sphere => (collisionWindow R).indicator
      (fun z => collisionMassClip K f z*massRegularizedPostRate N f z)
        (collisionGrouping.symm (p,q))) := (((collisionMassClip_measurable K hfm).mul
    (massRegularizedPostRate_measurable N hfm)).indicator (collisionWindow_measurable R)).comp
      collisionGrouping.symm.measurable |>.comp (measurable_const.prodMk measurable_id)
  have hci := hi.mono' hm.aestronglyMeasurable (ae_of_all _ (fun q => by
    rw [Real.norm_of_nonneg (hb _).1]
    exact (hb _).2))
  refine ⟨integral_nonneg (fun q => (hb _).1),?_⟩
  rw [gain_eq_full_integral hN.le]
  exact integral_mono hci hi (fun q => (hb _).2)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing the mass and elastic-window cutoffs from a physical gain fiber -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def clippedPostRate (K R : ℝ) (f : X × Velocity → ℝ) :
    (X × (Velocity × Velocity)) × Sphere → ℝ :=
  (collisionWindow R).indicator (fun z => collisionMassClip K f z*massNormalizedPostRate f z)

theorem clippedPostRate_measurable (K R : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (clippedPostRate K R f) :=
  ((collisionMassClip_measurable K hfm).mul (massNormalizedPostRate_measurable hfm)).indicator
    (collisionWindow_measurable R)

omit [MeasurableSpace X] in
theorem clippedPostRate_bounds {K R : ℝ} (hK : 0 ≤ K) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ clippedPostRate K R f z ∧ clippedPostRate K R f z ≤ postRate f z := by
  have hp : 0 ≤ postRate f z := preRate_nonneg hf _
  have hc := collisionMassClip_ratio_bounds hK hf z
  have he : collisionMassClip K f z*massNormalizedPostRate f z =
      (collisionMassClip K f z/(1+fiberMass volume f z.1.1))*postRate f z := by
    unfold massNormalizedPostRate
    ring
  by_cases hz : z ∈ collisionWindow R
  · rw [clippedPostRate,indicator_of_mem hz,he]
    exact ⟨mul_nonneg hc.1 hp, (mul_le_mul_of_nonneg_right hc.2 hp).trans_eq (one_mul _)⟩
  · rw [clippedPostRate,indicator_of_notMem hz]
    exact ⟨le_rfl,hp⟩

omit [MeasurableSpace X] in
theorem clippedPostRate_eventually_full {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    (fun n : ℕ => clippedPostRate (n:ℝ) (n:ℝ) f z) =ᶠ[atTop] fun _ => postRate f z := by
  filter_upwards [collisionMassClip_eventually_full hf z,
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (‖z.1.2.1‖+‖z.1.2.2‖))]
      with n hn hv
  have hw : z ∈ collisionWindow (n:ℝ) := by
    change ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ (n:ℝ)^2
    nlinarith [norm_nonneg z.1.2.1,norm_nonneg z.1.2.2,Nat.cast_nonneg (α := ℝ) n]
  rw [clippedPostRate,indicator_of_mem hw]
  exact hn.2

theorem clippedPhysicalGain_tendsto {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity)
    (hi : Integrable (fun q => postRate f (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea)) :
    Tendsto (fun n : ℕ => clippedPhysicalGain (n:ℝ) (n:ℝ) f p) atTop (𝓝 (gainDensity f p)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun q => postRate f (collisionGrouping.symm (p,q)))
    (fun n => ((clippedPostRate_measurable (n:ℝ) (n:ℝ) hfm).comp
      (collisionGrouping.symm.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable) hi
  · intro n
    filter_upwards [] with q
    change ‖clippedPostRate (n:ℝ) (n:ℝ) f (collisionGrouping.symm (p,q))‖ ≤ _
    rw [Real.norm_of_nonneg (clippedPostRate_bounds (Nat.cast_nonneg n) hf _).1]
    exact (clippedPostRate_bounds (Nat.cast_nonneg n) hf _).2
  · filter_upwards [] with q
    exact tendsto_const_nhds.congr' (clippedPostRate_eventually_full hf _).symm

theorem clippedPhysicalGain_nonneg {K R : ℝ} (hK : 0 ≤ K)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ clippedPhysicalGain K R f p :=
  integral_nonneg (fun q => (clippedPostRate_bounds hK hf (collisionGrouping.symm (p,q))).1)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual clipped gain converges along the same free characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

def characteristicClippedFiniteGain (N K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) :=
  TorusFlight.along (TorusFlight.regroup (clippedFiniteGain N K R f))

def characteristicClippedPhysicalGain (K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) :=
  TorusFlight.along (TorusFlight.regroup (clippedPhysicalGain K R f))

theorem characteristicClippedFiniteGain_measurable (N K R : ℝ)
    {f : (ℝ × Position) × Velocity → ℝ} (hf : Measurable f) :
    Measurable (characteristicClippedFiniteGain N K R f) :=
  (clippedFiniteGain_measurable N K R hf).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem characteristicClippedPhysicalGain_measurable (K R : ℝ)
    {f : (ℝ × Position) × Velocity → ℝ} (hf : Measurable f) :
    Measurable (characteristicClippedPhysicalGain K R f) :=
  (clippedPhysicalGain_measurable K R hf).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem GlobalCollisionLimit.characteristic_clipped_gain_limit {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (K : ℝ≥0) (L : ℝ) :
    Published.WeakL1Converges
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))))
      (fun n => characteristicClippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      (characteristicClippedPhysicalGain K R G.weakLimit.kineticProfile) ∧
    UniformIntegrable
      (fun n => characteristicClippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L)))) := by
  obtain ⟨hw,hu⟩ := G.clipped_gain_limit hf hi hT hR K
  have hm n := clippedFiniteGain_measurable ((G.weakLimit.indices n:ℝ)+1) (K:ℝ) R
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hwl := hw.restrict (s := (univ : Set (ℝ × Position)) ×ˢ Metric.closedBall (0:Velocity) L)
    (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)
  have hul := uniformIntegrable_restrict hu
    ((univ : Set (ℝ × Position)) ×ˢ Metric.closedBall (0:Velocity) L)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hwl hul
  exact ⟨TorusFlight.weak_along_regroup_local hm hwl,
    TorusFlight.uniformIntegrable_along_regroup_local hm hul⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
