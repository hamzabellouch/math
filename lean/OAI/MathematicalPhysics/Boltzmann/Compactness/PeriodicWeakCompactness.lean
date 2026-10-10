import OAI.MathematicalPhysics.Boltzmann.Branching.AveragingTailSources
import OAI.MathematicalPhysics.Boltzmann.Branching.CausalConvolution
import OAI.MathematicalPhysics.Boltzmann.Branching.CellLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.VelocityAveraging
import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.ProductKineticCutoff
import OAI.MathematicalPhysics.Boltzmann.Branching.RealL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.SupportedTransportTest
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainSmoothingAE
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedCollisionRates
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMomentEntropy
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicRenormalizedCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakConservedMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeLocalization
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusCharacteristic
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # Localized renormalized characteristics in Euclidean coordinates -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def projectedPhase (p : Velocity × Velocity) : Phase := (torusProjection p.1,p.2)

theorem projected_characteristic (p : Velocity × Velocity) (t : ℝ) :
    projectedPhase ((characteristic p t).1.2,(characteristic p t).2) =
      TorusFlight.flight t (projectedPhase p) := by
  apply Prod.ext
  · funext i
    change ((p.1 i+t*p.2 i : ℝ) : AddCircle (1:ℝ)) =
      (p.1 i : AddCircle (1:ℝ))+(t*p.2 i : ℝ)
    rw [AddCircle.coe_add]
  · rfl

def BoundedCutoffSolution.euclideanRenormalizedDensity (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : Published.KineticPhase) : ℝ :=
  S.renormalizedDensity β (z.1.1,projectedPhase (z.1.2,z.2))

def BoundedCutoffSolution.euclideanRenormalizedSource (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : Published.KineticPhase) : ℝ :=
  S.renormalizedSource β (z.1.1,projectedPhase (z.1.2,z.2))

theorem BoundedCutoffSolution.renormalized_localized_path (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (β : Renormalization)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (p : Phase) :
    χ t*S.renormalizedDensity β (t,TorusFlight.flight t p) =
      Real.exp (-t)*χ 0*(maxwellian p.2*β.toFun (f₀ p/maxwellian p.2))+
      ∫ r in 0..t, Real.exp (-(t-r))*(χ r*S.renormalizedSource β (r,TorusFlight.flight r p)+
        (deriv χ r+χ r)*S.renormalizedDensity β (r,TorusFlight.flight r p)) := by
  have he (r : ℝ) (hr : r ∈ Icc 0 t) :
      f₀ p+(∫ s in 0..r, S.source (s,TorusFlight.flight s p)-
        lossBound N*S.density (s,TorusFlight.flight s p)) = S.density (r,TorusFlight.flight r p) :=
    (S.characteristic_integral hN ⟨hr.1,hr.2.trans ht.2⟩ p).symm
  have h := β.localized_integral_path ht.1 (maxwellian_pos p.2)
    (S.collision_path_integrable hN p t)
    (fun r hr => (he r hr).symm ▸ S.nonnegative (r,TorusFlight.flight r p)) hχ
  rw [he t ⟨ht.1,le_rfl⟩] at h
  change _ = _+_ at h ⊢
  calc
    _ = _ := h
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.1] at hr
      dsimp only [renormalizedSource,renormalizedDensity,collision]
      rw [he r hr]
      rfl

theorem BoundedCutoffSolution.euclidean_renormalized_localized
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T)
    (β : Renormalization) {χ : Published.KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hzero : ∀ p, χ (characteristic p 0) = 0)
    (p : Velocity × Velocity) :
    χ (characteristic p t)*S.euclideanRenormalizedDensity β (characteristic p t) =
      ∫ r in 0..t, Real.exp (-(t-r))*(χ (characteristic p r)*
        S.euclideanRenormalizedSource β (characteristic p r)+
        (transportDerivative χ (characteristic p r)+χ (characteristic p r))*
          S.euclideanRenormalizedDensity β (characteristic p r)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (characteristic p) := by unfold characteristic; fun_prop
  have H := S.renormalized_localized_path hN ht β ((hχ.comp hc).of_le (by simp)) (projectedPhase p)
  have hder (r : ℝ) : deriv (fun r => χ (characteristic p r)) r =
      transportDerivative χ (characteristic p r) :=
    (TransportCutoff.hasDerivAt_along (hχ.differentiable (by simp)) p r).deriv
  dsimp only [Function.comp_def] at H
  rw [hzero,mul_zero,zero_mul,zero_add] at H
  have hd (r : ℝ) : S.euclideanRenormalizedDensity β (characteristic p r) =
      S.renormalizedDensity β (r,TorusFlight.flight r (projectedPhase p)) := by
    unfold euclideanRenormalizedDensity
    rw [projected_characteristic]
    rfl
  have hs (r : ℝ) : S.euclideanRenormalizedSource β (characteristic p r) =
      S.renormalizedSource β (r,TorusFlight.flight r (projectedPhase p)) := by
    unfold euclideanRenormalizedSource
    rw [projected_characteristic]
    rfl
  simpa only [hd,hs,hder] using H

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniformly integrable localized sources on the Euclidean fundamental cell -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N U : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.euclideanRenormalizedDensity_measurable
    (S : BoundedCutoffSolution N U f₀) (β : Renormalization) :
    Measurable (S.euclideanRenormalizedDensity β) :=
  (S.renormalizedDensity_measurable β).comp
    (measurable_fst.fst.prodMk ((TorusKineticChart.projection_measurable.comp
      measurable_fst.snd).prodMk measurable_snd))

theorem BoundedCutoffSolution.euclideanRenormalizedSource_measurable
    (S : BoundedCutoffSolution N U f₀) (β : Renormalization) :
    Measurable (S.euclideanRenormalizedSource β) :=
  (S.renormalizedSource_measurable β).comp
    (measurable_fst.fst.prodMk ((TorusKineticChart.projection_measurable.comp
      measurable_fst.snd).prodMk measurable_snd))

theorem approximatingSolution_renormalizedFields_cell_uniformIntegrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) :
    let S := fun n => approximatingSolution f hfm (n+Nat.ceil T)
    UniformIntegrable (fun n => (S n).euclideanRenormalizedDensity β) 1
      (TorusKineticChart.cellVolume T) ∧
    UniformIntegrable (fun n => (S n).euclideanRenormalizedSource β) 1
      (TorusKineticChart.cellVolume T) := by
  dsimp only
  constructor
  · apply Compactness.uniformIntegrable_of_comp_measurePreserving (TorusKineticChart.measurePreserving T)
      (fun n => (approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedDensity_measurable β)
    have h := approximatingSolution_renormalizedDensity_uniformIntegrable f hfm hf hi (T := T) β
    simpa only [Function.comp_def,BoundedCutoffSolution.euclideanRenormalizedDensity,
      BoundedCutoffSolution.renormalizedDensity,projectedPhase,TorusKineticChart.chart,
      TorusChart.projection_representative,BoundedCutoffSolution.kineticProfile,
      AnnularEnvelope.timePositionVolume] using h
  · apply Compactness.uniformIntegrable_of_comp_measurePreserving (TorusKineticChart.measurePreserving T)
      (fun n => (approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedSource_measurable β)
    have h := (approximatingSolution_renormalizedSources_uniformIntegrable f hfm hf hi hT β).2.2
    have he (n : ℕ) (p : (ℝ × Position) × Velocity) :
        collisionOperator (((n+Nat.ceil T:ℕ):ℝ)+1)
          (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile p =
        (approximatingSolution f hfm (n+Nat.ceil T)).collision (p.1.1,(p.1.2,p.2)) :=
      (approximatingSolution f hfm (n+Nat.ceil T)).kinetic_collision p
    dsimp only at h
    simp only [he] at h
    simpa only [Function.comp_def,BoundedCutoffSolution.euclideanRenormalizedSource,
      BoundedCutoffSolution.renormalizedSource,projectedPhase,TorusKineticChart.chart,
      TorusChart.projection_representative,BoundedCutoffSolution.kineticProfile,
      AnnularEnvelope.timePositionVolume] using h

theorem approximatingSolution_renormalizedLocalizedSource_uniformIntegrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T) (β : Renormalization)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) :
    UniformIntegrable (fun n => TransportCutoff.localizedSource T χ
      ((approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedDensity β)
      ((approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedSource β)) 1 volume := by
  obtain ⟨hd,hq⟩ := approximatingSolution_renormalizedFields_cell_uniformIntegrable f hfm hf hi hT β
  exact TorusKineticChart.localizedSource_uniformIntegrable hχ hc hs hd hq

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual renormalized approximants are localized transport resolvents -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T U : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.renormalized_resolvent (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hUT : U ≤ T) (β : Renormalization) {χ : Published.KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hzero : ∀ p, χ (characteristic p 0) = 0)
    (z : Published.KineticPhase) (ht : z.1.1 ∈ Icc 0 U) :
    χ z*S.euclideanRenormalizedDensity β z = Published.transportResolvent
      (localizedSource U χ (S.euclideanRenormalizedDensity β) (S.euclideanRenormalizedSource β)) z := by
  have h := S.euclidean_renormalized_localized hN ⟨ht.1,ht.2.trans hUT⟩ β hχ hzero
    (EuclideanFlight.flight (-z.1.1) (z.1.2,z.2))
  rw [EuclideanFlight.characteristic_endpoint] at h
  rw [TransportPrimitive.transportResolvent_eq
    (fun w hw => localizedSource_causal U χ _ _ w hw) z ht.1]
  rw [h]
  apply intervalIntegral.integral_congr
  intro t ht'
  rw [uIcc_of_le ht.1] at ht'
  dsimp only
  rw [EuclideanFlight.characteristic_back,localizedSource_on χ _ _ _ ⟨ht'.1,ht'.2.trans ht.2⟩]

theorem BoundedCutoffSolution.renormalized_average_resolvent
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) (hUT : U ≤ T) (β : Renormalization)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p, χ (characteristic p 0) = 0) (ψ : Velocity → ℝ)
    (z : Published.SpaceTime) (ht : z.1 ∈ Icc 0 U) :
    (∫ v, ψ v*(χ (z,v)*S.euclideanRenormalizedDensity β (z,v))) =
      Published.resolventAverage (localizedSource U χ (S.euclideanRenormalizedDensity β)
        (S.euclideanRenormalizedSource β)) ψ z := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => congrArg (fun a => ψ v*a)
    (S.renormalized_resolvent hN hUT β hχ hzero (z,v) ht))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual renormalized velocity averages have one common local subsequence -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_renormalized_average_compactness
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (T R : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (hR : ∀ j, 0 < R j)
    (β : ℕ → Renormalization) (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
    (hχx : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hχv : ∀ j, tsupport (χ j) ⊆ {z | ‖z.2‖ ≤ R j})
    (hχzero : ∀ j p, χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocallyIntegrable (g j) volume ∧ ∀ K : Set Published.SpaceTime, IsCompact K →
        K ⊆ {z | z.1 ∈ Icc 0 (T j)} →
        Tendsto (fun n => eLpNorm (fun z =>
          (∫ v, ψ j v*(χ j (z,v)*
            (approximatingSolution f hfm (φ n)).euclideanRenormalizedDensity (β j) (z,v)))-g j z)
          1 (volume.restrict K)) atTop (𝓝 0) := by
  let r : ℕ → ℕ → Published.KineticPhase → ℝ := fun j n => TransportCutoff.localizedSource (T j) (χ j)
    ((approximatingSolution f hfm n).euclideanRenormalizedDensity (β j))
    ((approximatingSolution f hfm n).euclideanRenormalizedSource (β j))
  have hs j n : ∀ᵐ z ∂(volume : Measure Published.KineticPhase), R j < ‖z.2‖ → r j n z = 0 :=
    ae_of_all _ (fun z hz => TransportCutoff.localizedSource_velocity_support (hχv j) _ _ z hz)
  have hui j : ∃ N : ℕ, UniformIntegrable (fun n => r j (n+N)) 1 volume :=
    ⟨Nat.ceil (T j),approximatingSolution_renormalizedLocalizedSource_uniformIntegrable
      f hfm hf hi (hT j) (β j) (hχ j) (hχc j) (hχx j)⟩
  obtain ⟨φ,g,hφ,hg⟩ := Published.glps1988Proposition3.countable_tail_sources_tests
    r R hR hs hui ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => ⟨(hg j).1,fun K hK hKT => ?_⟩⟩
  apply ((hg j).2 K hK).congr'
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (Nat.ceil (T j)))] with n hn
  have hbound : T j ≤ (φ n:ℝ)+1 := by
    have hc := Nat.le_ceil (T j)
    have hn' : (Nat.ceil (T j):ℝ) ≤ (φ n:ℝ) := by exact_mod_cast hn
    linarith
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have he := (approximatingSolution f hfm (φ n)).renormalized_average_resolvent
    (by positivity) hbound (β j) (hχ j) (hχzero j) (ψ j) z (hKT hz)
  exact congrArg (fun a => a-g j z) he.symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A single nonnegative global weak limit of the actual periodic approximants -/
noncomputable section
open MeasureTheory Filter Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

structure GlobalWeakLimit (f : Density) (hfm : Measurable f) where
  indices : ℕ → ℕ
  increasing : StrictMono indices
  density : ℝ × Phase → ℝ
  measurable : Measurable density
  nonnegative : ∀ z, 0 ≤ density z
  weighted_weak : Published.WeakL1Converges (finiteTimeMeasure.prod volume)
    (fun n => (approximatingSolution f hfm (indices n)).density) density

theorem exists_globalWeakLimit (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    Nonempty (GlobalWeakLimit f hfm) := by
  have hc := approximatingSolution_compactness_hypotheses f hfm hf hi finiteTimeMeasure
  obtain ⟨φ,g,hφ,hg⟩ := Published.l1WeakCompactnessInput _ _
    (fun n => (approximatingSolution f hfm n).kineticProfile_measurable) hc.1 hc.2
  have hw := TorusFlight.weak_regroup
    (fun n => (approximatingSolution f hfm (φ n)).kineticProfile_measurable) hg
  have hn := hw.nonneg (fun n => ae_of_all _ (approximatingSolution f hfm (φ n)).nonnegative)
  let G : ℝ × Phase → ℝ := fun z => max (TorusFlight.regroup g z) 0
  have he : TorusFlight.regroup g =ᵐ[finiteTimeMeasure.prod volume] G := by
    filter_upwards [hn] with z hz
    exact (max_eq_left hz).symm
  exact ⟨⟨φ,hφ,G,hw.1.max measurable_const,fun _ => le_max_right _ _,
    hw.congr_limit (hw.1.max measurable_const) he⟩⟩

theorem GlobalWeakLimit.weak_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges ((volume.restrict (Icc 0 T)).prod volume)
      (fun n => (approximatingSolution f hfm (G.indices n)).density) G.density :=
  weak_localize_time G.weighted_weak hT

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform rational approximation of the actual localized velocity averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_rational_averages_uniform (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {T C : ℝ}
    {w : Published.KineticPhase → ℝ} (hwm : Measurable w) (hb : ∀ z, |w z| ≤ C)
    (hs : ∀ z, z ∉ TorusKineticChart.region T → w z = 0) :
    Tendsto (fun k : ℕ => ⨆ n : ℕ, eLpNorm (fun z =>
      (∫ v, w (z,v)*TorusKineticChart.liftDensity (approximatingSolution f hfm n).kineticProfile (z,v))-
      (∫ v, w (z,v)*TorusKineticChart.liftDensity
        (rationalApproximation ((k:ℝ)+1) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
          (approximatingSolution f hfm n).kineticProfile) (z,v))) 1 volume) atTop (𝓝 0) := by
  let μ := (volume.restrict (Set.Icc 0 T)).prod (volume : Measure Position)
  have hm (n : ℕ) := (approximatingSolution f hfm n).kineticProfile_measurable
  have hn (n : ℕ) (p : (ℝ × Position) × Velocity) :
      0 ≤ (approximatingSolution f hfm n).kineticProfile p := (approximatingSolution f hfm n).nonnegative _
  have hfi n : Integrable (approximatingSolution f hfm n).kineticProfile (μ.prod volume) :=
    integrable_of_entropyGauge (hm n) (hn n)
      ((approximatingSolution f hfm n).kinetic_entropy_integrable (by positivity)
        (approximatingSolution_entropy f hfm hf hi n))
  have hr (k : ℕ) : 1 ≤ (k:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hgi (k n : ℕ) : Integrable (rationalApproximation ((k:ℝ)+1) (hr k)
      (approximatingSolution f hfm n).kineticProfile) (μ.prod volume) :=
    (Renormalization.rational _ (hr k)).weighted_integrable (hm n) (by unfold maxwellian; fun_prop)
      (hn n) (fun p => maxwellian_pos p.2) (hfi n)
  have hlim := approximatingSolution_rational_uniform_L1 f hfm hf hi (volume.restrict (Set.Icc 0 T))
  have hlim' := ENNReal.Tendsto.const_mul hlim (Or.inr (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top))
  simp only [mul_zero] at hlim'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim' (fun _ => bot_le)
  intro k
  apply iSup_le
  intro n
  apply (TorusKineticChart.average_lift_difference_le (hm n)
    (rationalApproximation_measurable (hr k) (hm n) (hn n)) hwm (hfi n) (hgi k n) hb hs).trans
  apply mul_le_mul' le_rfl
  exact le_iSup (fun n : ℕ => eLpNorm (fun p => (approximatingSolution f hfm n).kineticProfile p-
    rationalApproximation ((k:ℝ)+1) (hr k) (approximatingSolution f hfm n).kineticProfile p) 1 (μ.prod volume)) n

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Compactness of localized velocity averages of the original periodic densities -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_density_average_compactness
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 < R)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ)
    (hχx : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hχv : tsupport χ ⊆ {z | ‖z.2‖ ≤ R})
    (hχt : tsupport χ ⊆ {z | z.1.1 ∈ Icc 0 T})
    (hχzero : ∀ p, χ (TransportCutoff.characteristic p 0) = 0)
    {ψ : Velocity → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∃ (φ : ℕ → ℕ) (g : Published.SpaceTime → ℝ), StrictMono φ ∧ Integrable g ∧
      Tendsto (fun n => eLpNorm (fun z =>
        (∫ v, ψ v*(χ (z,v)*TorusKineticChart.liftDensity
          (approximatingSolution f hfm (φ n)).kineticProfile (z,v)))-g z) 1 volume) atTop (𝓝 0) := by
  let F := fun n => (approximatingSolution f hfm n).kineticProfile
  let b := fun k : ℕ => Renormalization.rational ((k:ℝ)+1) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  let w : Published.KineticPhase → ℝ := fun z => ψ z.2*χ z
  let A := fun (u : (ℝ × Position) × Velocity → ℝ) (z : Published.SpaceTime) =>
    ∫ v, w (z,v)*TorusKineticChart.liftDensity u (z,v)
  have hwm : Measurable w := (hψ.continuous.measurable.comp measurable_snd).mul hχ.continuous.measurable
  obtain ⟨C,hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  obtain ⟨B,hB⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hB0 : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hB 0)
  have hwb z : |w z| ≤ B*C := by
    rw [abs_mul]
    exact mul_le_mul (hB z.2) (hC z) (abs_nonneg _) hB0
  have hws z (hz : z ∉ TorusKineticChart.region T) : w z = 0 := by
    have hc : χ z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hz ⟨⟨hχt h,hχx h⟩,mem_univ _⟩
    exact mul_eq_zero_of_right (ψ z.2) hc
  obtain ⟨φ,g,hφ,hg⟩ := approximatingSolution_renormalized_average_compactness
    f hfm hf hi (fun _ => T) (fun _ => R) (fun _ => hT) (fun _ => hR) b
    (fun _ => χ) (fun _ => hχ) (fun _ => hχc) (fun _ => hχx) (fun _ => hχv)
    (fun _ => hχzero) (fun _ => ψ) (fun _ => hψ) (fun _ => hψc)
  let K : Set Published.SpaceTime := Prod.fst '' tsupport χ
  have hK : IsCompact K := hχc.isCompact.image continuous_fst
  have hKT : K ⊆ {z | z.1 ∈ Icc 0 T} := by
    rintro z ⟨p,hp,rfl⟩
    exact hχt hp
  have hAS (u : (ℝ × Position) × Velocity → ℝ) (z : Published.SpaceTime) (hz : z ∉ K) : A u z = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    have hc : χ (z,v) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      exact hz ⟨(z,v),hp,rfl⟩
    simp only [w,hc,mul_zero,zero_mul,Pi.zero_apply]
  let U := fun (k n : ℕ) => A (rationalApproximation ((k:ℝ)+1)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (F (φ n)))
  have hU k n z : U k n z = ∫ v, ψ v*(χ (z,v)*
      (approximatingSolution f hfm (φ n)).euclideanRenormalizedDensity (b k) (z,v)) := by
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [w,F,rationalApproximation,b,TorusKineticChart.liftDensity,
      BoundedCutoffSolution.kineticProfile,BoundedCutoffSolution.euclideanRenormalizedDensity,
      BoundedCutoffSolution.renormalizedDensity,projectedPhase,mul_assoc]
  have hUc k : Tendsto (fun n => eLpNorm (U k n-g k) 1 (volume.restrict K)) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm (fun z => U k n z-g k z) 1 (volume.restrict K)) atTop (𝓝 0)
    simpa only [hU] using (hg k).2 K hK hKT
  have hUg k := Compactness.supported_l1_limit hK.measurableSet
    (fun n z hz => hAS _ z hz) ((hg k).1.integrableOn_isCompact hK) (hUc k)
  have hFm n : Measurable (F n) := (approximatingSolution f hfm n).kineticProfile_measurable
  have hFi n : Integrable (F n) ((AnnularEnvelope.timePositionVolume T).prod volume) :=
    memLp_one_iff_integrable.mp
      ((approximatingSolution_compactness_hypotheses f hfm hf hi (volume.restrict (Icc 0 T))).1.memLp n)
  have hAi n : Integrable (A (F (φ n))) :=
    (TorusKineticChart.cutoff_liftDensity_integrable (hFm _) hwm (hFi _) hwb hws).integral_prod_left
  let δ := fun k : ℕ => ⨆ n : ℕ, eLpNorm (A (F n)-A (rationalApproximation ((k:ℝ)+1)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (F n))) 1 volume
  have hδ : Tendsto δ atTop (𝓝 0) := approximatingSolution_rational_averages_uniform f hfm hf hi hwm hwb hws
  obtain ⟨q,hqi,hq⟩ := Compactness.l1_limit_of_uniform_approximation hAi hδ
    (fun k n => le_iSup (fun n => eLpNorm (A (F n)-A (rationalApproximation ((k:ℝ)+1)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (F n))) 1 volume) (φ n))
    (fun k => (hUg k).2)
  refine ⟨φ,q,hφ,hqi,?_⟩
  change Tendsto (fun n => eLpNorm (fun z => A (F (φ n)) z-q z) 1 volume) atTop (𝓝 0) at hq
  simpa only [A,w,F,mul_assoc] using hq

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Choosing the global weak limit after a prescribed averaging subsequence -/
noncomputable section
open MeasureTheory Filter
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_globalWeakLimit_refining (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    ∃ (G : GlobalWeakLimit f hfm) (ρ : ℕ → ℕ), StrictMono ρ ∧ G.indices = σ ∘ ρ := by
  have hc := approximatingSolution_compactness_hypotheses f hfm hf hi finiteTimeMeasure
  have hui := Compactness.uniformIntegrable_comp hc.1 σ
  have hti := hc.2.comp σ
  obtain ⟨φ,g,hφ,hg⟩ := Published.l1WeakCompactnessInput _ _
    (fun n => (approximatingSolution f hfm (σ n)).kineticProfile_measurable) hui hti
  have hw := TorusFlight.weak_regroup
    (fun n => (approximatingSolution f hfm (σ (φ n))).kineticProfile_measurable) hg
  have hn := hw.nonneg (fun n => ae_of_all _ (approximatingSolution f hfm (σ (φ n))).nonnegative)
  let d : ℝ × Phase → ℝ := fun z => max (TorusFlight.regroup g z) 0
  have he : TorusFlight.regroup g =ᵐ[finiteTimeMeasure.prod volume] d := by
    filter_upwards [hn] with z hz
    exact (max_eq_left hz).symm
  exact ⟨⟨σ ∘ φ,hσ.comp hφ,d,hw.1.max measurable_const,fun _ => le_max_right _ _,
    hw.congr_limit (hw.1.max measurable_const) he⟩,φ,hφ,rfl⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One subsequence for countably many original-density velocity averages -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_countable_density_averages
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (times radii : ℕ → ℝ) (htimes : ∀ j, 0 ≤ times j) (hradii : ∀ j, 0 < radii j)
    (cutoffs : ℕ → Published.KineticPhase → ℝ)
    (hcuts : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (cutoffs j)) (hcutsc : ∀ j, HasCompactSupport (cutoffs j))
    (hcutsx : ∀ j, tsupport (cutoffs j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hcutsv : ∀ j, tsupport (cutoffs j) ⊆ {z | ‖z.2‖ ≤ radii j})
    (hcutst : ∀ j, tsupport (cutoffs j) ⊆ {z | z.1.1 ∈ Icc 0 (times j)})
    (hcutszero : ∀ j p, cutoffs j (TransportCutoff.characteristic p 0) = 0)
    (tests : ℕ → Velocity → ℝ) (htests : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (tests j))
    (htestsc : ∀ j, HasCompactSupport (tests j)) :
    ∃ (φ : ℕ → ℕ) (q : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Integrable (q j) ∧
        Tendsto (fun n => eLpNorm (fun z =>
          (∫ v, tests j v*(cutoffs j (z,v)*TorusKineticChart.liftDensity
            (approximatingSolution f hfm (φ n)).kineticProfile (z,v)))-q j z) 1 volume) atTop (𝓝 0) := by
  let F := fun n => (approximatingSolution f hfm n).kineticProfile
  let b := fun k : ℕ => Renormalization.rational ((k:ℝ)+1) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  obtain ⟨φ,G,hφ,hG⟩ := approximatingSolution_renormalized_average_compactness
    f hfm hf hi (fun i => times (Nat.unpair i).1) (fun i => radii (Nat.unpair i).1)
    (fun i => htimes _) (fun i => hradii _) (fun i => b (Nat.unpair i).2)
    (fun i => cutoffs (Nat.unpair i).1) (fun i => hcuts _) (fun i => hcutsc _)
    (fun i => hcutsx _) (fun i => hcutsv _) (fun i => hcutszero _)
    (fun i => tests (Nat.unpair i).1) (fun i => htests _) (fun i => htestsc _)
  have hex (j : ℕ) : ∃ q : Published.SpaceTime → ℝ, Integrable q ∧
      Tendsto (fun n => eLpNorm (fun z =>
        (∫ v, tests j v*(cutoffs j (z,v)*TorusKineticChart.liftDensity
          (F (φ n)) (z,v)))-q z) 1 volume) atTop (𝓝 0) := by
    let T := times j
    let χ := cutoffs j
    let ψ := tests j
    have hT := htimes j
    have hχ := hcuts j
    have hχc := hcutsc j
    have hχx := hcutsx j
    have hχt := hcutst j
    have hψ := htests j
    have hψc := htestsc j
    let g := fun k => G (Nat.pair j k)
    have hg (k : ℕ) : LocallyIntegrable (g k) volume ∧
        ∀ K : Set Published.SpaceTime, IsCompact K → K ⊆ {z | z.1 ∈ Icc 0 T} →
        Tendsto (fun n => eLpNorm (fun z =>
          (∫ v, ψ v*(χ (z,v)*(approximatingSolution f hfm (φ n)).euclideanRenormalizedDensity (b k) (z,v)))-g k z)
          1 (volume.restrict K)) atTop (𝓝 0) := by
      simpa only [Nat.unpair_pair] using hG (Nat.pair j k)
    let w : Published.KineticPhase → ℝ := fun z => ψ z.2*χ z
    let A := fun (u : (ℝ × Position) × Velocity → ℝ) (z : Published.SpaceTime) =>
      ∫ v, w (z,v)*TorusKineticChart.liftDensity u (z,v)
    have hwm : Measurable w := (hψ.continuous.measurable.comp measurable_snd).mul hχ.continuous.measurable
    obtain ⟨C,hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    obtain ⟨B,hB⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    have hB0 : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hB 0)
    have hwb z : |w z| ≤ B*C := by
      rw [abs_mul]
      exact mul_le_mul (hB z.2) (hC z) (abs_nonneg _) hB0
    have hws z (hz : z ∉ TorusKineticChart.region T) : w z = 0 := by
      have hc : χ z = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hz ⟨⟨hχt h,hχx h⟩,mem_univ _⟩
      exact mul_eq_zero_of_right (ψ z.2) hc
    let K : Set Published.SpaceTime := Prod.fst '' tsupport χ
    have hK : IsCompact K := hχc.isCompact.image continuous_fst
    have hKT : K ⊆ {z | z.1 ∈ Icc 0 T} := by
      rintro z ⟨p,hp,rfl⟩
      exact hχt hp
    have hAS (u : (ℝ × Position) × Velocity → ℝ) (z : Published.SpaceTime) (hz : z ∉ K) : A u z = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with v
      have hc : χ (z,v) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hp
        exact hz ⟨(z,v),hp,rfl⟩
      simp only [w,hc,mul_zero,zero_mul,Pi.zero_apply]
    let U := fun (k n : ℕ) => A (rationalApproximation ((k:ℝ)+1)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (F (φ n)))
    have hU k n z : U k n z = ∫ v, ψ v*(χ (z,v)*
        (approximatingSolution f hfm (φ n)).euclideanRenormalizedDensity (b k) (z,v)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [w,F,rationalApproximation,b,TorusKineticChart.liftDensity,
        BoundedCutoffSolution.kineticProfile,BoundedCutoffSolution.euclideanRenormalizedDensity,
        BoundedCutoffSolution.renormalizedDensity,projectedPhase,mul_assoc]
    have hUc k : Tendsto (fun n => eLpNorm (U k n-g k) 1 (volume.restrict K)) atTop (𝓝 0) := by
      change Tendsto (fun n => eLpNorm (fun z => U k n z-g k z) 1 (volume.restrict K)) atTop (𝓝 0)
      simpa only [hU] using (hg k).2 K hK hKT
    have hUg k := Compactness.supported_l1_limit hK.measurableSet
      (fun n z hz => hAS _ z hz) ((hg k).1.integrableOn_isCompact hK) (hUc k)
    have hFm n : Measurable (F n) := (approximatingSolution f hfm n).kineticProfile_measurable
    have hFi n : Integrable (F n) ((AnnularEnvelope.timePositionVolume T).prod volume) :=
      memLp_one_iff_integrable.mp
        ((approximatingSolution_compactness_hypotheses f hfm hf hi (volume.restrict (Icc 0 T))).1.memLp n)
    have hAi n : Integrable (A (F (φ n))) :=
      (TorusKineticChart.cutoff_liftDensity_integrable (hFm _) hwm (hFi _) hwb hws).integral_prod_left
    let δ := fun k : ℕ => ⨆ n : ℕ, eLpNorm (A (F n)-A (rationalApproximation ((k:ℝ)+1)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (F n))) 1 volume
    have hδ : Tendsto δ atTop (𝓝 0) := approximatingSolution_rational_averages_uniform f hfm hf hi hwm hwb hws
    obtain ⟨q,hqi,hq⟩ := Compactness.l1_limit_of_uniform_approximation hAi hδ
      (fun k n => le_iSup (fun n => eLpNorm (A (F n)-A (rationalApproximation ((k:ℝ)+1)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (F n))) 1 volume) (φ n))
      (fun k => (hUg k).2)
    refine ⟨q,hqi,?_⟩
    change Tendsto (fun n => eLpNorm (fun z => A (F (φ n)) z-q z) 1 volume) atTop (𝓝 0) at hq
    simpa only [A,w,F,mul_assoc] using hq
  choose q hq using hex
  exact ⟨φ,q,hφ,hq⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Weak velocity averages of the same global periodic limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def GlobalWeakLimit.kineticProfile {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (p : (ℝ × Position) × Velocity) : ℝ :=
  G.density (p.1.1,(p.1.2,p.2))

theorem GlobalWeakLimit.kineticProfile_measurable {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) : Measurable G.kineticProfile :=
  G.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

theorem GlobalWeakLimit.kinetic_weak_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)
      (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile) G.kineticProfile := by
  apply Published.WeakL1Converges.of_comp_measurePreserving
    (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm
    (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
    G.kineticProfile_measurable
  exact G.weak_on_window hT

theorem GlobalWeakLimit.lifted_weak_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges (TorusKineticChart.cellVolume T)
      (fun n => TorusKineticChart.liftDensity (approximatingSolution f hfm (G.indices n)).kineticProfile)
      (TorusKineticChart.liftDensity G.kineticProfile) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (TorusKineticChart.measurePreserving T)
    (fun n => TorusKineticChart.liftDensity_measurable
      (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
    (TorusKineticChart.liftDensity_measurable G.kineticProfile_measurable)
  simpa only [TorusKineticChart.liftDensity_comp,AnnularEnvelope.timePositionVolume] using G.kinetic_weak_on_window hT

theorem GlobalWeakLimit.average_weak_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T C : ℝ} (hT : 0 ≤ T) {w : Published.KineticPhase → ℝ}
    (hw : Measurable w) (hb : ∀ z, |w z| ≤ C) :
    Published.WeakL1Converges
      ((volume.restrict (Icc 0 T)).prod (volume.restrict TorusChart.cube))
      (fun n z => ∫ v, w (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))
      (fun z => ∫ v, w (z,v)*TorusKineticChart.liftDensity G.kineticProfile (z,v)) := by
  have hFi n : Integrable (approximatingSolution f hfm (G.indices n)).kineticProfile
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) :=
    memLp_one_iff_integrable.mp ((approximatingSolution_compactness_hypotheses f hfm hf hi
      (volume.restrict (Icc 0 T))).1.memLp (G.indices n))
  have hLift n : Integrable (TorusKineticChart.liftDensity
      (approximatingSolution f hfm (G.indices n)).kineticProfile) (TorusKineticChart.cellVolume T) := by
    apply ((TorusKineticChart.measurePreserving T).integrable_comp
      (TorusKineticChart.liftDensity_measurable
        (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable).aestronglyMeasurable).mp
    simpa only [TorusKineticChart.liftDensity_comp,AnnularEnvelope.timePositionVolume] using hFi n
  exact (G.lifted_weak_on_window hT).marginal hLift hw C hb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong localized averages have the actual global weak limit as their limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.average_weak {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T C : ℝ} (hT : 0 ≤ T) {w : Published.KineticPhase → ℝ}
    (hw : Measurable w) (hb : ∀ z, |w z| ≤ C)
    (hs : ∀ z, z ∉ TorusKineticChart.region T → w z = 0) :
    Published.WeakL1Converges volume
      (fun n z => ∫ v, w (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))
      (fun z => ∫ v, w (z,v)*TorusKineticChart.liftDensity G.kineticProfile (z,v)) := by
  have hz (u : (ℝ × Position) × Velocity → ℝ) z
      (hz : z ∉ Icc 0 T ×ˢ TorusChart.cube) :
      (∫ v, w (z,v)*TorusKineticChart.liftDensity u (z,v)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    have hv : (z,v) ∉ TorusKineticChart.region T := fun h => hz h.1
    simp only [hs _ hv,zero_mul,Pi.zero_apply]
  have h := G.average_weak_on_window hf hi hT hw hb
  rw [Measure.prod_restrict] at h
  exact h.of_restrict_support (measurableSet_Icc.prod TorusChart.measurableSet_cube)
    (fun n => hz _) (hz _)

theorem GlobalWeakLimit.average_strong_identification {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T C : ℝ} (hT : 0 ≤ T) {w : Published.KineticPhase → ℝ}
    (hw : Measurable w) (hb : ∀ z, |w z| ≤ C)
    (hs : ∀ z, z ∉ TorusKineticChart.region T → w z = 0)
    {q : Published.SpaceTime → ℝ} (hq : Integrable q)
    (hc : Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, w (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-q z) 1 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, w (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      (∫ v, w (z,v)*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume) atTop (𝓝 0) := by
  have hFi n : Integrable (approximatingSolution f hfm (G.indices n)).kineticProfile
      ((AnnularEnvelope.timePositionVolume T).prod volume) :=
    memLp_one_iff_integrable.mp ((approximatingSolution_compactness_hypotheses f hfm hf hi
      (volume.restrict (Icc 0 T))).1.memLp (G.indices n))
  have hAi n : Integrable (fun z => ∫ v, w (z,v)*TorusKineticChart.liftDensity
      (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v)) :=
    (TorusKineticChart.cutoff_liftDensity_integrable
      (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable hw (hFi n) hb hs).integral_prod_left
  have he := (G.average_weak hf hi hT hw hb hs).eq_of_strong hAi hq hc
  have hn n : eLpNorm (fun z =>
      (∫ v, w (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-q z) 1 volume =
      eLpNorm (fun z =>
      (∫ v, w (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      (∫ v, w (z,v)*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  simpa only [hn] using hc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Mass-normalized pair compactness for the actual global approximation sequence -/
noncomputable section
open MeasureTheory Filter
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_normalizedPair_compactness
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    UniformIntegrable (fun n => Compactness.normalizedPair volume
      (approximatingSolution f hfm n).kineticProfile) 1
      ((μ.prod (volume : Measure Position)).prod (volume.prod volume)) ∧
    UnifTight (fun n => Compactness.normalizedPair volume
      (approximatingSolution f hfm n).kineticProfile) 1
      ((μ.prod (volume : Measure Position)).prod (volume.prod volume)) := by
  have hm := fun n => (approximatingSolution f hfm n).kineticProfile_measurable
  have hn : ∀ (n : ℕ) (p : (ℝ × Position) × Velocity),
      0 ≤ (approximatingSolution f hfm n).kineticProfile p :=
    fun n p => (approximatingSolution f hfm n).nonnegative _
  have hg := fun n => (approximatingSolution f hfm n).kinetic_entropy_integrable
    (μ := μ) (by positivity) (approximatingSolution_entropy f hfm hf hi n)
  have hb := fun n => (approximatingSolution f hfm n).kinetic_entropy_integral_le
    (μ := μ) (by positivity) (approximatingSolution_entropy f hfm hf hi n)
  exact ⟨Compactness.normalizedPair_uniformIntegrable hm hn hg hb,
    Compactness.normalizedPair_unifTight hm hn hg hb⟩

def GlobalWeakLimit.subsequence {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {φ : ℕ → ℕ} (hφ : StrictMono φ) : GlobalWeakLimit f hfm where
  indices := G.indices ∘ φ
  increasing := G.increasing.comp hφ
  density := G.density
  measurable := G.measurable
  nonnegative := G.nonnegative
  weighted_weak := G.weighted_weak.comp hφ.tendsto_atTop

theorem GlobalWeakLimit.exists_normalizedPair_limit {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ),
      Published.WeakL1Converges
        ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume))
        (fun n => Compactness.normalizedPair volume
          (approximatingSolution f hfm ((G.subsequence hφ).indices n)).kineticProfile) W := by
  have h := approximatingSolution_normalizedPair_compactness f hfm hf hi finiteTimeMeasure
  have hm (n : ℕ) : Measurable (Compactness.normalizedPair volume
      (approximatingSolution f hfm (G.indices n)).kineticProfile) :=
    Compactness.normalizedTensor_measurable
      (Compactness.fiberMass_measurable (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
      (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable
      (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable
  let : SigmaFinite (volume : Measure (Velocity × Velocity)) := by
    change SigmaFinite ((volume : Measure Velocity).prod (volume : Measure Velocity))
    infer_instance
  obtain ⟨φ,W,hφ,hW⟩ := Published.l1WeakCompactnessInput
    ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume : Measure (Velocity × Velocity))) _ hm
    (Compactness.uniformIntegrable_comp h.1 G.indices) (h.2.comp G.indices)
  exact ⟨φ,hφ,W,hW⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A single global weak limit with strongly convergent density averages -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_globalWeakLimit_with_averages
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (times radii : ℕ → ℝ) (htimes : ∀ j, 0 ≤ times j) (hradii : ∀ j, 0 < radii j)
    (cutoffs : ℕ → Published.KineticPhase → ℝ)
    (hcuts : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (cutoffs j)) (hcutsc : ∀ j, HasCompactSupport (cutoffs j))
    (hcutsx : ∀ j, tsupport (cutoffs j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hcutsv : ∀ j, tsupport (cutoffs j) ⊆ {z | ‖z.2‖ ≤ radii j})
    (hcutst : ∀ j, tsupport (cutoffs j) ⊆ {z | z.1.1 ∈ Icc 0 (times j)})
    (hcutszero : ∀ j p, cutoffs j (TransportCutoff.characteristic p 0) = 0)
    (tests : ℕ → Velocity → ℝ) (htests : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (tests j))
    (htestsc : ∀ j, HasCompactSupport (tests j)) :
    ∃ G : GlobalWeakLimit f hfm, ∀ j,
      Tendsto (fun n => eLpNorm (fun z =>
        (∫ v, tests j v*(cutoffs j (z,v)*TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v)))-
        (∫ v, tests j v*(cutoffs j (z,v)*TorusKineticChart.liftDensity
          G.kineticProfile (z,v)))) 1 volume) atTop (𝓝 0) := by
  obtain ⟨φ,q,hφ,hq⟩ := approximatingSolution_countable_density_averages f hfm hf hi
    times radii htimes hradii cutoffs hcuts hcutsc hcutsx hcutsv hcutst hcutszero tests htests htestsc
  obtain ⟨G,ρ,hρ,hG⟩ := exists_globalWeakLimit_refining f hfm hf hi hφ
  refine ⟨G,fun j => ?_⟩
  let w : Published.KineticPhase → ℝ := fun z => tests j z.2*cutoffs j z
  have hwm : Measurable w := ((htests j).continuous.measurable.comp measurable_snd).mul
    (hcuts j).continuous.measurable
  obtain ⟨C,hC⟩ := (hcuts j).continuous.bounded_above_of_compact_support (hcutsc j)
  obtain ⟨B,hB⟩ := (htests j).continuous.bounded_above_of_compact_support (htestsc j)
  have hB0 : 0 ≤ B := (abs_nonneg (tests j 0)).trans (hB 0)
  have hwb z : |w z| ≤ B*C := by
    rw [abs_mul]
    exact mul_le_mul (hB z.2) (hC z) (abs_nonneg _) hB0
  have hws z (hz : z ∉ TorusKineticChart.region (times j)) : w z = 0 := by
    have hc : cutoffs j z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hz ⟨⟨hcutst j h,hcutsx j h⟩,mem_univ _⟩
    exact mul_eq_zero_of_right _ hc
  have hc := (hq j).2.comp hρ.tendsto_atTop
  have hc' : Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, w (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-q j z) 1 volume) atTop (𝓝 0) := by
    rw [hG]
    change Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, tests j v*(cutoffs j (z,v)*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (φ (ρ n))).kineticProfile (z,v)))-q j z) 1 volume) atTop (𝓝 0) at hc
    simpa only [w,Function.comp_apply,mul_assoc] using hc
  have h := G.average_strong_identification hf hi (htimes j) hwm hwb hws (hq j).1 hc'
  simpa only [w,mul_assoc] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform velocity-tail control for localized actual periodic densities -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_patch_velocity_tail
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T C R : ℝ} (hR : 0 < R) {χ : Published.SpaceTime → ℝ}
    (hχ : Measurable χ) (hC : ∀ z, |χ z| ≤ C)
    (hχs : ∀ z, z ∉ Icc 0 T ×ˢ TorusChart.cube → χ z = 0)
    {β : Velocity → ℝ} (hβm : Measurable β)
    (hβ0 : ∀ v, 0 ≤ β v) (hβ1 : ∀ v, β v ≤ 1) (hβeq : ∀ v, ‖v‖ ≤ R → β v = 1)
    (n : ℕ) :
    eLpNorm (fun z : Published.KineticPhase =>
      χ z.1*TorusKineticChart.liftDensity (approximatingSolution f hfm n).kineticProfile z-
      β z.2*(χ z.1*TorusKineticChart.liftDensity (approximatingSolution f hfm n).kineticProfile z))
      1 volume ≤ ENNReal.ofReal (C*((volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f)/R^2) := by
  let F := (approximatingSolution f hfm n).kineticProfile
  let d : (ℝ × Position) × Velocity → ℝ := fun p => F p-β p.2*F p
  have hFm : Measurable F := (approximatingSolution f hfm n).kineticProfile_measurable
  have hdm : Measurable d := hFm.sub ((hβm.comp measurable_snd).mul hFm)
  have hw : Measurable (fun z : Published.KineticPhase => χ z.1) := hχ.comp measurable_fst
  have hs (z : Published.KineticPhase) (hz : z ∉ TorusKineticChart.region T) : χ z.1 = 0 := by
    apply hχs
    intro h
    exact hz ⟨h,mem_univ _⟩
  have hbound := TorusKineticChart.cutoff_liftDensity_L1_bound hdm hw (fun z => hC z.1) hs
  have htail := velocityCutoff_L1_bound hR hFm
    (fun p => (approximatingSolution f hfm n).nonnegative _) hβm hβ0 hβ1 hβeq
    ((approximatingSolution f hfm n).kinetic_entropy_integrable (μ := volume.restrict (Icc 0 T))
      (by positivity) (approximatingSolution_entropy f hfm hf hi n))
    ((approximatingSolution f hfm n).kinetic_entropy_integral_le (μ := volume.restrict (Icc 0 T))
      (by positivity) (approximatingSolution_entropy f hfm hf hi n))
  have he : (fun z : Published.KineticPhase =>
      χ z.1*TorusKineticChart.liftDensity F z-β z.2*(χ z.1*TorusKineticChart.liftDensity F z)) =
      (fun z => χ z.1*TorusKineticChart.liftDensity d z) := by
    funext z
    dsimp only [d,TorusKineticChart.liftDensity]
    ring
  rw [he]
  refine hbound.trans ((mul_le_mul' le_rfl htail).trans_eq ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  rw [← ENNReal.ofReal_mul hC0]
  congr 1
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Simultaneous original-density averages on interior spacetime patches -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_globalWeakLimit_patch_averages
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (χ : ℕ → Published.SpaceTime → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
    (hχs : ∀ j, tsupport (χ j) ⊆ TorusKineticChart.interiorRegion)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i)) :
    ∃ G : GlobalWeakLimit f hfm, ∀ s i,
      Tendsto (fun n => eLpNorm (fun z =>
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
        atTop (𝓝 0) := by
  choose β hβ hβc _hβn hβeq using fun i => Compactness.exists_velocity_cutoff (hψc i)
  choose R hR hRball using fun i => (hβc i).isBounded.subset_ball_lt 0 (0 : Velocity)
  choose T hT hTball using fun s => (hχc s).isBounded.subset_ball_lt 0 (0 : Published.SpaceTime)
  let cuts : ℕ → Published.KineticPhase → ℝ := fun n =>
    Compactness.productCutoff (χ (Nat.unpair n).1) (β (Nat.unpair n).2)
  have hcutsc n : HasCompactSupport (cuts n) := Compactness.productCutoff_compact (hχc _) (hβc _)
  have hcuts n : ContDiff ℝ (⊤ : ℕ∞) (cuts n) := Compactness.productCutoff_smooth (hχ _) (hβ _)
  have hcutsx n : tsupport (cuts n) ⊆ {z | z.1.2 ∈ TorusChart.cube} :=
    Compactness.productCutoff_in_cell _ (hχs _)
  have hcutsv n : tsupport (cuts n) ⊆ {z | ‖z.2‖ ≤ R (Nat.unpair n).2} := by
    intro z hz
    have hb := (Compactness.productCutoff_tsupport _ _ hz).2
    have hr := hRball (Nat.unpair n).2 hb
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hr)
  have hcutst n : tsupport (cuts n) ⊆ {z | z.1.1 ∈ Icc 0 (T (Nat.unpair n).1)} := by
    intro z hz
    have hc := (Compactness.productCutoff_tsupport _ _ hz).1
    have hp := hχs (Nat.unpair n).1 hc
    have ht := hTball (Nat.unpair n).1 hc
    have hnorm : ‖z.1‖ < T (Nat.unpair n).1 := by simpa only [Metric.mem_ball,dist_zero_right] using ht
    have hcoord : |z.1.1| ≤ ‖z.1‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z.1
    exact ⟨le_of_lt hp.1,(le_abs_self _).trans (hcoord.trans hnorm.le)⟩
  obtain ⟨G,hG⟩ := exists_globalWeakLimit_with_averages f hfm hf hi
    (fun n => T (Nat.unpair n).1) (fun n => R (Nat.unpair n).2)
    (fun n => (hT _).le) (fun n => hR _) cuts hcuts hcutsc hcutsx hcutsv hcutst
    (fun n => Compactness.productCutoff_initial_zero _ (hχs _))
    (fun n => ψ (Nat.unpair n).2) (fun n => hψ _) (fun n => hψc _)
  refine ⟨G,fun s i => ?_⟩
  have he (z : Published.SpaceTime) (v : Velocity) (a : ℝ) :
      ψ i v*(cuts (Nat.pair s i) (z,v)*a) = χ s z*(ψ i v*a) := by
    simp only [cuts,Nat.unpair_pair,Compactness.productCutoff]
    calc
      _ = χ s z*((ψ i v*β i v)*a) := by ring
      _ = _ := by rw [hβeq i v]
  have hc := hG (Nat.pair s i)
  simp only [Nat.unpair_pair] at hc
  simpa only [he,integral_const_mul] using hc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Finite-window Euclidean charts for the actual normalized pairs -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem weak_pair_on_window
    {F : ℕ → (ℝ × Position) × (Velocity × Velocity) → ℝ}
    {W : (ℝ × Position) × (Velocity × Velocity) → ℝ}
    (hW : Published.WeakL1Converges
      ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume)) F W)
    {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume)) F W := by
  have hw := (windowInverseWeight_measurable T).comp
    (measurable_fst.fst : Measurable (fun z : (ℝ × Position) × (Velocity × Velocity) => z.1.1))
  have h := hW.withDensity_bounded hw
    (fun z => windowInverseWeight_nonneg T z.1.1)
    ⟨Real.exp (T^2),fun z => windowInverseWeight_bound hT z.1.1⟩
  have he := prod_withDensity_left
    (μ := finiteTimeMeasure.prod (volume : Measure Position))
    (ν := (volume : Measure Velocity).prod (volume : Measure Velocity))
    ((windowInverseWeight_measurable T).comp measurable_fst).ennreal_ofReal
  simp only [Function.comp_apply] at h he
  rw [← he,← prod_withDensity_left (windowInverseWeight_measurable T).ennreal_ofReal,
    finiteTimeMeasure_reweight] at h
  exact h

theorem normalizedPair_lift (F : (ℝ × Position) × Velocity → ℝ) :
    Compactness.normalizedPair volume (TorusKineticChart.liftDensity F) =
      TorusKineticChart.liftPair (Compactness.normalizedPair volume F) := rfl

theorem normalizedPair_lifted_weak
    {F : ℕ → (ℝ × Position) × Velocity → ℝ} (hF : ∀ n, Measurable (F n))
    {W : (ℝ × Position) × (Velocity × Velocity) → ℝ}
    (hW : Published.WeakL1Converges
      ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume))
      (fun n => Compactness.normalizedPair volume (F n)) W)
    {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges
      ((TorusKineticChart.baseVolume T).prod (volume.prod volume))
      (fun n => Compactness.normalizedPair volume (TorusKineticChart.liftDensity (F n)))
      (TorusKineticChart.liftPair W) := by
  have hm n : Measurable (Compactness.normalizedPair volume (F n)) :=
    Compactness.normalizedTensor_measurable (Compactness.fiberMass_measurable (ν := volume) (hF n)) (hF n) (hF n)
  have h := weak_pair_on_window hW hT
  apply Published.WeakL1Converges.of_comp_measurePreserving
    (TorusKineticChart.pair_measurePreserving T)
    (fun n => (TorusKineticChart.liftPair_measurable (hm n)))
    (TorusKineticChart.liftPair_measurable hW.1)
  simpa only [TorusKineticChart.liftPair_comp,AnnularEnvelope.timePositionVolume,
    Measure.volume_eq_prod] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual entropy and mass-marginal bounds in the Euclidean periodic cell -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_cell_entropy_integrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (T : ℝ) (n : ℕ) :
    Integrable (entropyGauge (TorusKineticChart.liftDensity
      (approximatingSolution f hfm n).kineticProfile))
      ((TorusKineticChart.baseVolume T).prod volume) := by
  have hm := entropyGauge_measurable (approximatingSolution f hfm n).kineticProfile_measurable
  apply ((TorusKineticChart.measurePreserving T).integrable_comp
    (TorusKineticChart.liftDensity_measurable hm).aestronglyMeasurable).mp
  simpa only [TorusKineticChart.liftDensity_comp,AnnularEnvelope.timePositionVolume] using
    (approximatingSolution f hfm n).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi n)

theorem approximatingSolution_cell_entropy_le
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (T : ℝ) (n : ℕ) :
    (∫ z, entropyGauge (TorusKineticChart.liftDensity
      (approximatingSolution f hfm n).kineticProfile) z
      ∂(TorusKineticChart.baseVolume T).prod volume) ≤
      (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f := by
  have hm := entropyGauge_measurable (approximatingSolution f hfm n).kineticProfile_measurable
  have he := Published.integral_comp_measurePreserving (TorusKineticChart.measurePreserving T)
    (TorusKineticChart.liftDensity_measurable hm)
  have he' : (∫ z, entropyGauge (approximatingSolution f hfm n).kineticProfile z
      ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) =
      (∫ z, entropyGauge (TorusKineticChart.liftDensity
        (approximatingSolution f hfm n).kineticProfile) z
        ∂(TorusKineticChart.baseVolume T).prod volume) := by
    simp only [← Function.comp_def,TorusKineticChart.liftDensity_comp] at he
    exact he
  rw [← he']
  exact (approximatingSolution f hfm n).kinetic_entropy_integral_le
    (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi n)

theorem approximatingSolution_cell_mass_uniformIntegrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (T : ℝ) :
    UniformIntegrable (fun n => Compactness.fiberMass volume
      (TorusKineticChart.liftDensity (approximatingSolution f hfm n).kineticProfile))
      1 (TorusKineticChart.baseVolume T) :=
  mass_marginal_uniformIntegrable
    (fun n => TorusKineticChart.liftDensity_measurable
      (approximatingSolution f hfm n).kineticProfile_measurable)
    (fun n _ => (approximatingSolution f hfm n).nonnegative _)
    (approximatingSolution_cell_entropy_integrable f hfm hf hi T)
    (approximatingSolution_cell_entropy_le f hfm hf hi T)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy and velocity moments of the actual global weak limit -/
noncomputable section
open MeasureTheory Filter Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

variable {f : Density} {hfm : Measurable f}

theorem relativeEntropy_of_weak_approximation
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {μ : Measure ℝ} [IsFiniteMeasure μ] {φ : ℕ → ℕ} {g : ℝ × Phase → ℝ}
    (hg : Published.WeakL1Converges (μ.prod volume)
      (fun n => (approximatingSolution f hfm (φ n)).density) g)
    (hgn : ∀ z, 0 ≤ g z) :
    Integrable (spacetimeRelativeEntropy g) (μ.prod volume) ∧
      (∫ z, spacetimeRelativeEntropy g z ∂μ.prod volume) ≤ μ.real univ*initialEntropyBudget f := by
  have hE n := approximatingSolution_spacetimeEntropy_integrable f hfm hf hi (φ n) μ
  have hH n := approximatingSolution_spacetimeRelativeEntropy f hfm hf hi (φ n) μ
  exact hg.entropy_bound
    (fun n => density_integrable_of_spacetimeEntropy
      (approximatingSolution f hfm (φ n)).measurable (approximatingSolution f hfm (φ n)).nonnegative (hE n))
    (fun n => ae_of_all _ (approximatingSolution f hfm (φ n)).nonnegative)
    (ae_of_all _ hgn) (by unfold maxwellian; fun_prop)
    (integrable_maxwellian_phase.comp_snd μ) (ae_of_all _ (fun z => maxwellian_pos z.2.2))
    (fun n => (hH n).1) (mul_nonneg (by positivity) (initialEntropyBudget_nonneg f hf))
    (Eventually.of_forall (fun n => (hH n).2))

theorem GlobalWeakLimit.entropy_on_window (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (spacetimeRelativeEntropy G.density) ((volume.restrict (Icc 0 T)).prod volume) ∧
      (∫ z, spacetimeRelativeEntropy G.density z ∂(volume.restrict (Icc 0 T)).prod volume) ≤
        (volume.restrict (Icc 0 T)).real univ*initialEntropyBudget f :=
  relativeEntropy_of_weak_approximation hf hi (G.weak_on_window hT) G.nonnegative

theorem GlobalWeakLimit.entropyMoment_on_window (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (spacetimeEntropy G.density) ((volume.restrict (Icc 0 T)).prod volume) :=
  spacetimeEntropy_integrable_of_relativeEntropy G.measurable G.nonnegative
    (G.entropy_on_window hf hi hT).1

theorem GlobalWeakLimit.finiteEntropy_ae (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), FiniteEntropyDatum (fun p => G.density (t,p)) := by
  filter_upwards [(G.entropyMoment_on_window hf hi hT).prod_right_ae] with t ht
  exact ⟨ae_of_all _ (fun p => G.nonnegative (t,p)),
    (G.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,ht⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The original datum controls entropy in the global weak limit -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {f : Density} {hfm : Measurable f}

theorem relativeEntropy_of_weak_approximation_sharp
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {μ : Measure ℝ} [IsFiniteMeasure μ] {φ : ℕ → ℕ} {g : ℝ × Phase → ℝ}
    (hφ : StrictMono φ)
    (hg : Published.WeakL1Converges (μ.prod volume)
      (fun n => (approximatingSolution f hfm (φ n)).density) g)
    (hgn : ∀ z, 0 ≤ g z) :
    (∫ z, spacetimeRelativeEntropy g z ∂μ.prod volume) ≤ μ.real univ*relativeEntropy f := by
  have hE n := approximatingSolution_spacetimeEntropy_integrable f hfm hf hi (φ n) μ
  have hH n := approximatingSolution_spacetimeRelativeEntropy f hfm hf hi (φ n) μ
  have hbound n : (∫ z, spacetimeRelativeEntropy (approximatingSolution f hfm (φ n)).density z ∂μ.prod volume) ≤
      μ.real univ*relativeEntropy (initialApproximation ((φ n:ℝ)+1) f) :=
    spacetimeRelativeEntropy_integral_le (hH n).1
      ((approximatingSolution f hfm (φ n)).relativeEntropy_all_times (by positivity) (by positivity))
  have ht := ((initialApproximation_relativeEntropy_tendsto hfm hf hi).comp hφ.tendsto_atTop).const_mul (μ.real univ)
  have hC : 0 ≤ μ.real univ*relativeEntropy f :=
    mul_nonneg (by positivity) (relativeEntropy_nonneg ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩)
  apply le_of_forall_pos_le_add
  intro ε hε
  have he := ht.eventually (gt_mem_nhds (show μ.real univ*relativeEntropy f < μ.real univ*relativeEntropy f+ε by linarith))
  have hcut := hg.entropy_bound
    (fun n => density_integrable_of_spacetimeEntropy
      (approximatingSolution f hfm (φ n)).measurable (approximatingSolution f hfm (φ n)).nonnegative (hE n))
    (fun n => ae_of_all _ (approximatingSolution f hfm (φ n)).nonnegative)
    (ae_of_all _ hgn) (by unfold maxwellian; fun_prop)
    (integrable_maxwellian_phase.comp_snd μ) (ae_of_all _ (fun z => maxwellian_pos z.2.2))
    (fun n => (hH n).1) (add_nonneg hC hε.le) (he.mono (fun n hn => (hbound n).trans hn.le))
  exact hcut.2

theorem GlobalWeakLimit.entropy_ae (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂finiteTimeMeasure, relativeEntropy (fun p => G.density (t,p)) ≤ relativeEntropy f := by
  have hI := (relativeEntropy_of_weak_approximation hf hi G.weighted_weak G.nonnegative).1
  apply ae_le_of_forall_setIntegral_le
    (f := fun t => relativeEntropy (fun p => G.density (t,p)))
    (g := fun _ => relativeEntropy f) ?_ (integrable_const _) ?_
  · convert hI.integral_prod_left using 1
    funext t
    apply integral_congr_ae
    exact ae_of_all _ (fun p => (scalarRelativeEntropy_eq (maxwellian_pos p.2) _).symm)
  · intro s hs _hsfin
    have hw := G.weighted_weak.restrict_base hs
    have hh := relativeEntropy_of_weak_approximation_sharp hf hi G.increasing hw G.nonnegative
    have hIs := (relativeEntropy_of_weak_approximation hf hi hw G.nonnegative).1
    rw [integral_prod _ hIs] at hh
    have he (t : ℝ) : (∫ p, spacetimeRelativeEntropy G.density (t,p)) =
        relativeEntropy (fun p => G.density (t,p)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
    simpa only [he,integral_const,smul_eq_mul] using hh

theorem GlobalWeakLimit.finiteEntropy_ae_volume (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, FiniteEntropyDatum (fun p => G.density (t,p)) ∧
      relativeEntropy (fun p => G.density (t,p)) ≤ relativeEntropy f := by
  have hI := spacetimeEntropy_integrable_of_relativeEntropy G.measurable G.nonnegative
    (relativeEntropy_of_weak_approximation hf hi G.weighted_weak G.nonnegative).1
  have htime : ∀ᵐ t ∂finiteTimeMeasure, FiniteEntropyDatum (fun p => G.density (t,p)) ∧
      relativeEntropy (fun p => G.density (t,p)) ≤ relativeEntropy f := by
    filter_upwards [hI.prod_right_ae,G.entropy_ae hf hi] with t ht hH
    exact ⟨⟨ae_of_all _ (fun p => G.nonnegative (t,p)),
      (G.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,ht⟩,hH⟩
  have hac : (volume : Measure ℝ) ≪ finiteTimeMeasure :=
    withDensity_absolutelyContinuous' timeWeight_measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun t => (ENNReal.ofReal_pos.mpr (timeWeight_pos t)).ne'))
  exact hac.ae_le htime

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
