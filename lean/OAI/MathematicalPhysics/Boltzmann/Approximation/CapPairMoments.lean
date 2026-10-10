import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Branching.AveragingTailSources
import OAI.MathematicalPhysics.Boltzmann.Branching.CellLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanBackwardMap
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPairWindowGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.SpacetimeRelativeEntropy
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakCapOuterBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusCharacteristic

namespace OAI

section

/-! # A compatible global weak limit for the actual hot pair products -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotPairExtraction.pairLimit (E : HotPairExtraction S) (z : HotPairPhase) : ℝ :=
  max 0 (liminf (fun j => E.pairProfile j z) atTop)

theorem HotPairExtraction.pairLimit_measurable (E : HotPairExtraction S) :
    Measurable E.pairLimit :=
  measurable_const.max (Measurable.liminf (fun j => (E.pairWeak j).1))

theorem HotPairExtraction.pairLimit_nonneg (E : HotPairExtraction S) (z : HotPairPhase) :
    0 ≤ E.pairLimit z := le_max_left _ _

theorem HotPairExtraction.pairLimit_eq_local (E : HotPairExtraction S) (j : ℕ) :
    E.pairLimit =ᵐ[hotPairWindowVolume (j+1) (j+1)] E.pairProfile j := by
  have he (k : ℕ) : ∀ᵐ z ∂hotPairWindowVolume (j+1) (j+1),
      j ≤ k → E.pairProfile k z = E.pairProfile j z := by
    by_cases hjk : j ≤ k
    · exact (E.compatible hjk).mono (fun _ hz _ => hz)
    · exact ae_of_all _ (fun _ h => (hjk h).elim)
  filter_upwards [ae_all_iff.mpr he,E.pairNonneg j] with z hz hn
  have hevent : (fun k => E.pairProfile k z) =ᶠ[atTop] (fun _ => E.pairProfile j z) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hz k hk
  have ht : Tendsto (fun k => E.pairProfile k z) atTop (𝓝 (E.pairProfile j z)) :=
    (tendsto_congr' hevent).mpr tendsto_const_nhds
  exact (congrArg (max (0:ℝ)) ht.liminf_eq).trans (max_eq_right hn)

theorem HotPairExtraction.pairLimit_weak (E : HotPairExtraction S) (A R : ℝ) :
    Published.WeakL1Converges (hotPairWindowVolume A R)
      (fun n => CollisionCompactness.pairProduct (S.hotDensity (E.indices n))) E.pairLimit := by
  obtain ⟨j,hj⟩ := exists_nat_gt (max A R)
  have hA : A ≤ (j:ℝ)+1 := by have := (le_max_left A R).trans_lt hj; linarith
  have hR : R ≤ (j:ℝ)+1 := by have := (le_max_right A R).trans_lt hj; linarith
  have hw := (E.pairWeak j).congr_limit E.pairLimit_measurable (E.pairLimit_eq_local j).symm
  have h := hw.restrict (hotPairWindowSet_measurable A R)
  rw [hotPairWindowVolume_restrict hA hR] at h
  exact h

def HotPairExtraction.subsequence (E : HotPairExtraction S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : HotPairExtraction S where
  toHotLimitExtraction := E.toHotLimitExtraction.subsequence φ hφ
  pairProfile := E.pairProfile
  pairWeak := fun j => (E.pairWeak j).comp hφ.tendsto_atTop
  pairNonneg := E.pairNonneg

theorem HotPairExtraction.subsequence_pairLimit (E : HotPairExtraction S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : (E.subsequence φ hφ).pairLimit = E.pairLimit := rfl

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The hot pair limit in the physical Euclidean averaging coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotPairChart : (Published.SpaceTime × (Velocity × Velocity)) ≃ᵐ
    JetCopyDatum.AttainedCapSequence.HotPairPhase :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) spaceEquiv)
    (MeasurableEquiv.refl (Velocity × Velocity))

theorem hotPairChart_measurePreserving (A R : ℝ) : MeasurePreserving hotPairChart
    ((hotBaseVolume A R).prod volume)
    (JetCopyDatum.AttainedCapSequence.hotPairWindowVolume A R) := by
  have hs : MeasurePreserving spaceEquiv (volume : Measure Velocity) volume := by
    convert JetPeriodicDatum.spatialMap_measurePreserving using 1
    funext x
    exact spaceEquiv_apply x
  exact ((MeasurePreserving.id (volume.restrict (Icc (0:ℝ) A))).prod
    (hs.restrict_preimage measurableSet_closedBall)).prod (MeasurePreserving.id volume)

end BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.physical_pair_weak (E : HotPairExtraction S) (hs₀ : 0 < s₀)
    {A : ℝ} (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges (hotPairWindowVolume A R)
      (fun n => CollisionCompactness.pairProduct (S.physicalHotDensity (E.indices n)))
      E.pairLimit := by
  apply (E.pairLimit_weak A R).congr_eventually
  filter_upwards [S.eventually_extendedHot_eq hs₀ E.horizon_limit hA] with n hn
  rw [hotPairWindowVolume_eq]
  filter_upwards [ae_restrict_mem (hotPairWindowSet_measurable A R)] with z hz
  change S.extendedHot (E.indices n) (z.1.1,(z.1.2,z.2.1))*
      S.extendedHot (E.indices n) (z.1.1,(z.1.2,z.2.2)) =
    S.rescaledHot (E.indices n) (z.1.1,(z.1.2,z.2.1))*
      S.rescaledHot (E.indices n) (z.1.1,(z.1.2,z.2.2))
  rw [hn z.1.1 hz.1.1 (z.1.2,z.2.1),hn z.1.1 hz.1.1 (z.1.2,z.2.2)]

theorem euclideanHot_pair_eq_chart (S : AttainedCapSequence F) (n : ℕ) :
    CollisionCompactness.pairProduct (S.euclideanHot n) =
      CollisionCompactness.pairProduct (S.physicalHotDensity n) ∘ EuclideanFlight.hotPairChart := by
  funext z
  simp only [CollisionCompactness.pairProduct,euclideanHot_eq_chart,Function.comp_apply]
  rfl

theorem HotPairExtraction.euclidean_pair_weak (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ}
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
      (fun n => CollisionCompactness.pairProduct (S.euclideanHot (E.indices n)))
      (E.pairLimit ∘ EuclideanFlight.hotPairChart) := by
  have h := (E.physical_pair_weak hs₀ hA R).comp_measurableEquiv EuclideanFlight.hotPairChart
    (EuclideanFlight.hotPairChart_measurePreserving A R)
    (fun n => CollisionCompactness.pairProduct_measurable
      (S.physicalHotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq _))
  simpa only [euclideanHot_pair_eq_chart] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weighted hot pair limits in physical Euclidean coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclideanHot_weighted_pair_eq_chart (S : AttainedCapSequence F) (n : ℕ) :
    CollisionCompactness.pairDensity (S.euclideanHot n) =
      CollisionCompactness.pairDensity (S.physicalHotDensity n) ∘ EuclideanFlight.hotPairChart := by
  funext z
  simp only [CollisionCompactness.pairDensity,euclideanHot_eq_chart,Function.comp_apply]
  rfl

theorem weighted_pair_physical_weak (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A R : ℝ} (hA : ENNReal.ofReal A < U) {W : HotPairPhase → ℝ}
    (hW : Published.WeakL1Converges (hotPairWindowVolume A R)
      (fun n => CollisionCompactness.pairDensity (S.hotDensity (κ n))) W) :
    Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
      (fun n => CollisionCompactness.pairDensity (S.euclideanHot (κ n)))
      (W ∘ EuclideanFlight.hotPairChart) := by
  have hp : Published.WeakL1Converges (hotPairWindowVolume A R)
      (fun n => CollisionCompactness.pairDensity (S.physicalHotDensity (κ n))) W := by
    apply hW.congr_eventually
    filter_upwards [S.eventually_extendedHot_eq hs₀ hU hA] with n hn
    rw [hotPairWindowVolume_eq]
    filter_upwards [ae_restrict_mem (hotPairWindowSet_measurable A R)] with z hz
    change (1+‖z.2.1‖+‖z.2.2‖)*S.extendedHot (κ n) (z.1.1,(z.1.2,z.2.1))*
        S.extendedHot (κ n) (z.1.1,(z.1.2,z.2.2)) =
      (1+‖z.2.1‖+‖z.2.2‖)*S.rescaledHot (κ n) (z.1.1,(z.1.2,z.2.1))*
        S.rescaledHot (κ n) (z.1.1,(z.1.2,z.2.2))
    rw [hn z.1.1 hz.1.1 (z.1.2,z.2.1),hn z.1.1 hz.1.1 (z.1.2,z.2.2)]
  have h := hp.comp_measurableEquiv EuclideanFlight.hotPairChart
    (EuclideanFlight.hotPairChart_measurePreserving A R)
    (fun n => CollisionCompactness.pairDensity_measurable
      (S.physicalHotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq _))
  simpa only [euclideanHot_weighted_pair_eq_chart] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Integrable physical weighted hot pairs after a finite prefix -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.eventually_weighted_pair_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    ∀ᶠ n in atTop, Integrable (CollisionCompactness.pairDensity (S.euclideanHot (E.indices n)))
      ((EuclideanFlight.hotBaseVolume A R).prod volume) := by
  have hui := (S.hotWeightedPair_bounds hs₀ hsmax hη hηmax hK hd₀ hq hA0 R).1
  filter_upwards [S.eventually_extendedHot_eq hs₀ E.horizon_limit hA] with n hn
  have hi := memLp_one_iff_integrable.mp (hui.memLp (E.indices n))
  have he : CollisionCompactness.pairDensity (S.hotDensity (E.indices n))
      =ᵐ[hotPairWindowVolume A R]
        CollisionCompactness.pairDensity (S.physicalHotDensity (E.indices n)) := by
    rw [hotPairWindowVolume_eq]
    filter_upwards [ae_restrict_mem (hotPairWindowSet_measurable A R)] with z hz
    change (1+‖z.2.1‖+‖z.2.2‖)*S.extendedHot (E.indices n) (z.1.1,(z.1.2,z.2.1))*
        S.extendedHot (E.indices n) (z.1.1,(z.1.2,z.2.2)) =
      (1+‖z.2.1‖+‖z.2.2‖)*S.rescaledHot (E.indices n) (z.1.1,(z.1.2,z.2.1))*
        S.rescaledHot (E.indices n) (z.1.1,(z.1.2,z.2.2))
    rw [hn z.1.1 hz.1.1 (z.1.2,z.2.1),hn z.1.1 hz.1.1 (z.1.2,z.2.2)]
  have hp := (EuclideanFlight.hotPairChart_measurePreserving A R).integrable_comp_of_integrable
    (hi.congr he)
  simpa only [euclideanHot_weighted_pair_eq_chart] using hp

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Applying the published averaging input to the actual cap family -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.averaging_subsequence (hGLPS : Published.GLPS1988Proposition3)
    {s₀ η K α γ d₀ q : ℝ} (F : CompactCapFamily s₀ η K α γ d₀ q)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.LocalL1Converges (fun n => Published.resolventAverage
        (localizedSource F.time χ (EuclideanFlight.density q (F.approximation (φ n)).solution.value)
          (EuclideanFlight.source ((φ n)+1) q (F.approximation (φ n)).solution.value)) (ψ j)) (g j) := by
  have hcompact : IsCompact (Prod.snd '' tsupport χ) := hc.image continuous_snd
  obtain ⟨R,hR,hball⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : Velocity)
  have hv : tsupport χ ⊆ {z : KineticPhase | ‖z.2‖ ≤ R} := by
    intro z hz
    have hb := hball (mem_image_of_mem Prod.snd hz)
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hb : ‖z.2‖ < R).le
  let r : ℕ → KineticPhase → ℝ := fun n => localizedSource F.time χ
    (EuclideanFlight.density q (F.approximation n).solution.value)
    (EuclideanFlight.source (n+1) q (F.approximation n).solution.value)
  have hr : ∀ n, ∀ᵐ z ∂(volume : Measure KineticPhase), R < ‖z.2‖ → r n z = 0 := by
    intro n
    exact ae_of_all _ (fun z hz => localizedSource_velocity_support hv _ _ z hz)
  exact hGLPS.countable_tests (R := R) r hR hr (F.localized_source_ui hχ hc hs) ψ hψ hψc

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Eventual integrability of the unextended hot pair products -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.eventually_pair_integrable (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    ∀ᶠ n in atTop, Integrable (CollisionCompactness.pairProduct (S.euclideanHot (E.indices n)))
      ((EuclideanFlight.hotBaseVolume A R).prod volume) := by
  have hui := (S.hotPair_bounds hs₀ hsmax hη hηmax hK hd₀ hq hA0 R).1
  filter_upwards [S.eventually_extendedHot_eq hs₀ E.horizon_limit hA] with n hn
  have hi := memLp_one_iff_integrable.mp (hui.memLp (E.indices n))
  have he : CollisionCompactness.pairProduct (S.hotDensity (E.indices n))
      =ᵐ[hotPairWindowVolume A R]
        CollisionCompactness.pairProduct (S.physicalHotDensity (E.indices n)) := by
    rw [hotPairWindowVolume_eq]
    filter_upwards [ae_restrict_mem (hotPairWindowSet_measurable A R)] with z hz
    change S.extendedHot (E.indices n) (z.1.1,(z.1.2,z.2.1))*
        S.extendedHot (E.indices n) (z.1.1,(z.1.2,z.2.2)) =
      S.rescaledHot (E.indices n) (z.1.1,(z.1.2,z.2.1))*
        S.rescaledHot (E.indices n) (z.1.1,(z.1.2,z.2.2))
    rw [hn z.1.1 hz.1.1 (z.1.2,z.2.1),hn z.1.1 hz.1.1 (z.1.2,z.2.2)]
  have hp := (EuclideanFlight.hotPairChart_measurePreserving A R).integrable_comp_of_integrable
    (hi.congr he)
  simpa only [euclideanHot_pair_eq_chart] using hp

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Identification of a hot pair tensor moment from strong averaged products -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.pair_moment_of_strong (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A R : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon)
    {k l : Published.KineticPhase → ℝ} (hk : Continuous k) (hl : Continuous l)
    (hkc : HasCompactSupport k) (hlc : HasCompactSupport l)
    {D : Set Published.SpaceTime} (hD : IsCompact D)
    (hDw : D ⊆ EuclideanFlight.hotBaseSet A R)
    (hstrong : Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, k (z,v)*S.euclideanHot (E.indices n) (z,v))*
        (∫ w, l (z,w)*S.euclideanHot (E.indices n) (z,w))-
      (∫ v, k (z,v)*E.toHotLimitExtraction.hotLimit (EuclideanFlight.hotChart (z,v)))*
        (∫ w, l (z,w)*E.toHotLimitExtraction.hotLimit (EuclideanFlight.hotChart (z,w)))) 1
        (volume.restrict D)) atTop (𝓝 0)) :
    (fun z => ∫ y : Velocity × Velocity, (k (z,y.1)*l (z,y.2))*
      E.pairLimit (EuclideanFlight.hotPairChart (z,y))) =ᵐ[volume.restrict D]
      (fun z => (∫ v, k (z,v)*E.toHotLimitExtraction.hotLimit (EuclideanFlight.hotChart (z,v)))*
        (∫ w, l (z,w)*E.toHotLimitExtraction.hotLimit (EuclideanFlight.hotChart (z,w)))) := by
  have : SFinite (EuclideanFlight.hotBaseVolume A R) := by
    unfold EuclideanFlight.hotBaseVolume
    infer_instance
  have hw := (E.euclidean_pair_weak hs₀ hsmax hη hηmax hK hd₀ hq hA R).restrict_base
    hD.measurableSet
  rw [EuclideanFlight.hotBaseVolume_eq,Measure.restrict_restrict_of_subset hDw] at hw
  have hi : ∀ᶠ n in atTop, Integrable (CollisionCompactness.pairProduct
      (S.euclideanHot (E.indices n))) ((volume.restrict D).prod (volume : Measure (Velocity × Velocity))) := by
    filter_upwards [E.eventually_pair_integrable hs₀ hsmax hη hηmax hK hd₀ hq hA0 hA R]
      with n hn
    rw [EuclideanFlight.hotBaseVolume_eq] at hn
    exact hn.mono_measure (Measure.prod_mono (Measure.restrict_mono hDw le_rfl) le_rfl)
  rw [show (volume : Measure (Velocity × Velocity)) =
    (volume : Measure Velocity).prod volume from Measure.volume_eq_prod Velocity Velocity] at hw hi
  obtain ⟨C,hC⟩ := hk.bounded_above_of_compact_support hkc
  obtain ⟨B,hB⟩ := hl.bounded_above_of_compact_support hlc
  have h := Published.weak_pair_moment_of_strong_product hw hi hk.measurable hl.measurable
    C B hC hB hstrong
  simpa only [Function.comp_apply,← Measure.volume_eq_prod] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Local strong convergence of velocity averages of the actual cap solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.averages_resolvent (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) (ψ : Velocity → ℝ) :
    (fun z : Published.SpaceTime => ∫ v, ψ v*(χ (z,v)*EuclideanFlight.density q F.solution.value (z,v)))
      =ᵐ[Published.timeSpaceVolume T]
      Published.resolventAverage (localizedSource T χ (EuclideanFlight.density q F.solution.value)
        (EuclideanFlight.source (N+1) q F.solution.value)) ψ := by
  have hi : Measurable (initial s₀ η K α γ d₀ q N
      (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)) :=
    (measurable_seed s₀ η K α γ d₀ q N).add
      ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have hA : 0 < F.amplitude := F.amplitude_pos
  exact EuclideanFlight.velocity_averages_resolvent hcarleman F.solution hq₁ hq₂
    (by positivity) (by positivity) le_rfl hi hχ hzero ψ

theorem CompactCapFamily.physical_averages_subsequence
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    {s₀ η K α γ d₀ q : ℝ} (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ (z,v)*EuclideanFlight.density q (F.approximation (φ n)).solution.value (z,v))) (g j) := by
  obtain ⟨φ,g,hφ,hg⟩ := F.averaging_subsequence hGLPS hχ hc hs ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => (hg j).time_restrict (fun n => ?_)⟩
  exact (F.approximation (φ n)).averages_resolvent hcarleman hq₁ hq₂ hχ hzero (ψ j)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Simultaneous averaging without losing the actual weak density and pair limits -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.countable_physical_averages
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    {s₀ η K α γ d₀ q : ℝ} (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) (a : ℕ → ℕ)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ j (z,v)*EuclideanFlight.density q (F.approximation (a (φ n))).solution.value (z,v)))
        (g j) := by
  have hex (j) : ∃ R : ℝ, 0 < R ∧ tsupport (χ j) ⊆
      {z : Published.KineticPhase | ‖z.2‖ ≤ R} := by
    obtain ⟨R,hR,hball⟩ := ((hc j).image continuous_snd).isBounded.subset_ball_lt 0 (0 : Velocity)
    refine ⟨R,hR,fun z hz => ?_⟩
    have hb := hball (mem_image_of_mem Prod.snd hz)
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hb : ‖z.2‖ < R).le
  choose R hR hv using hex
  let r : ℕ → ℕ → Published.KineticPhase → ℝ := fun j n => localizedSource F.time (χ j)
    (EuclideanFlight.density q (F.approximation (a n)).solution.value)
    (EuclideanFlight.source (a n+1) q (F.approximation (a n)).solution.value)
  have hr (j n) : ∀ᵐ z ∂(volume : Measure Published.KineticPhase), R j < ‖z.2‖ → r j n z = 0 :=
    ae_of_all _ (fun z hz => localizedSource_velocity_support (hv j) _ _ z hz)
  have hui (j) : UniformIntegrable (r j) 1 volume :=
    Compactness.uniformIntegrable_comp (F.localized_source_ui (hχ j) (hc j) (hs j)) a
  obtain ⟨φ,g,hφ,hg⟩ := hGLPS.countable_sources_tests r R hR hr hui ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => (hg j).time_restrict (fun n => ?_)⟩
  exact (F.approximation (a (φ n))).averages_resolvent hcarleman hq₁ hq₂ (hχ j) (hzero j) (ψ j)

theorem TightCapFamily.exists_weak_and_average_limits
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ)
      (A : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ j (z,v)*EuclideanFlight.density q (F.approximation (φ n)).solution.value (z,v))) (A j)) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  obtain ⟨a,g,W,ha,hg,hW,hgn,hWn⟩ := F.exists_weak_limits hDP
  obtain ⟨b,A,hb,hA⟩ := F.toCompactCapFamily.countable_physical_averages hcarleman hGLPS
    hq₁ hq₂ a χ hχ hc hs hzero ψ hψ hψc
  exact ⟨a ∘ b,g,W,A,ha.comp hb,hg.comp hb.tendsto_atTop,hW.comp hb.tendsto_atTop,hA,hgn,hWn⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Factorized velocity-pair moments of actual cap-family weak limits -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

def averageWeight (χ : Published.KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (z : Published.KineticPhase) : ℝ := ψ z.2*χ z

theorem TightCapFamily.exists_factorized_pair_moments
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ i j (S : Set Published.SpaceTime), IsCompact S →
        (fun x => ∫ y : Velocity × Velocity,
          (averageWeight (χ i) (ψ i) (x,y.1)*averageWeight (χ j) (ψ j) (x,y.2))*
            TorusKineticChart.liftPair W (x,y)) =ᵐ[(TorusKineticChart.baseVolume F.time).restrict S]
          (fun x => (∫ v, averageWeight (χ i) (ψ i) (x,v)*TorusKineticChart.liftDensity g (x,v))*
            (∫ w, averageWeight (χ j) (ψ j) (x,w)*TorusKineticChart.liftDensity g (x,w)))) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  obtain ⟨φ,g,W,A,hφ,hg,hW,hA,hgn,hWn⟩ :=
    F.exists_weak_and_average_limits hcarleman hGLPS hDP hq₁ hq₂ χ hχ hc hs hzero ψ hψ hψc
  refine ⟨φ,g,W,hφ,hg,hW,?_,hgn,hWn⟩
  let f : ℕ → Published.KineticPhase → ℝ := fun n =>
    EuclideanFlight.density q (F.approximation (φ n)).solution.value
  have hfm (n) : Measurable (f n) :=
    EuclideanFlight.density_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfi (n) : Integrable (f n) ((TorusKineticChart.baseVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactCapFamily.density_ui_cell.memLp (φ n))
  have hpUI := Compactness.uniformIntegrable_comp F.toCompactCapFamily.raw_pairs_ui_cell φ
  have hgw := TorusKineticChart.weak_density_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hg
  have hWw := TorusKineticChart.weak_pair_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hW
  have hkw (j) : Continuous (averageWeight (χ j) (ψ j)) :=
    ((hψ j).continuous.comp continuous_snd).mul (hχ j).continuous
  have hkc (j) : HasCompactSupport (averageWeight (χ j) (ψ j)) := (hc j).mul_left
  have hAw (j) : Published.TimeLocalL1Converges F.time
      (fun n x => ∫ v, averageWeight (χ j) (ψ j) (x,v)*f n (x,v)) (A j) := by
    simpa only [averageWeight,mul_assoc] using hA j
  intro i j S hS
  exact Published.local_pair_moment_factorization (TorusKineticChart.baseVolume_le F.time)
    hfm hfi hpUI hgw hWw (hkw i) (hkw j) (hkc i) (hkc j) (hAw i) (hAw j) hS

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
