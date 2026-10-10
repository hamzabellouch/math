import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotSourceIntegrability
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapPairMoments
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveNonlinearLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedAverageProducts
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanBackwardMap
import OAI.MathematicalPhysics.Boltzmann.Branching.HotChartHomeomorph
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.ProductKineticCutoff
import OAI.MathematicalPhysics.Boltzmann.Branching.VanishingCutoffCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Collision.WeightLocalL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalMomentIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchIdentity
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairRepresentative
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakConservedMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdCentralVanishing

namespace OAI

section

/-! # Global L¹ convergence for every chosen compact interior hot average -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem HotLimitExtraction.global_strong_averages
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (S : AttainedCapSequence F) (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ) (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | 0 < z.1.1 ∧ ENNReal.ofReal z.1.1 < E.horizon})
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j,
      Tendsto (fun n => eLpNorm (fun z =>
        (∫ v, ψ j v*(χ j (z,v)*S.euclideanHot (E.indices (φ n)) (z,v)))-
        (∫ v, ψ j v*(χ j (z,v)*E.hotLimit (EuclideanFlight.hotChart (z,v))))) 1 volume)
        atTop (𝓝 0) := by
  choose a A R ha haA hA hwin using fun j =>
    exists_positive_cutoff_window E.horizon_ge (hc j) (hs j)
  obtain ⟨φ,hφ,hconv⟩ := E.strong_averages hcarleman hGLPS S hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ a A R ha haA hA χ hχ hc hwin ψ hψ hψc
  refine ⟨φ,hφ,fun j => ?_⟩
  let D := Prod.fst '' tsupport (χ j)
  have hD : IsCompact D := (hc j).image continuous_fst
  have hspace : Continuous (fun z : Published.SpaceTime => EuclideanFlight.spaceEquiv z.2) :=
    EuclideanFlight.spaceEquiv_continuous.comp continuous_snd
  obtain ⟨B,_hB,hball⟩ := (hD.image hspace).isBounded.subset_ball_lt 0
    (0 : JetPrototype.Space)
  have hDw : D ⊆ EuclideanFlight.hotBaseSet (A j) B := by
    rintro z ⟨u,hu,rfl⟩
    refine ⟨⟨(ha j).le.trans (hwin j hu).1.1.1,(hwin j hu).1.1.2⟩,?_⟩
    exact Metric.ball_subset_closedBall (hball (mem_image_of_mem _ (mem_image_of_mem Prod.fst hu)))
  have ht := hconv j B D hD hDw
  apply ht.congr
  intro n
  exact (EuclideanFlight.average_difference_norm_restrict (hc j) (ψ j)
    (S.euclideanHot (E.indices (φ n))) (E.hotLimit ∘ EuclideanFlight.hotChart)).symm

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Strong local convergence of products of actual hot velocity averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem HotLimitExtraction.strong_average_products
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (S : AttainedCapSequence F) (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ) (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | 0 < z.1.1 ∧ ENNReal.ofReal z.1.1 < E.horizon})
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j (D : Set Published.SpaceTime), IsCompact D →
      Tendsto (fun n => eLpNorm (fun z =>
        (∫ v, ψ i v*(χ i (z,v)*S.euclideanHot (E.indices (φ n)) (z,v)))*
          (∫ v, ψ j v*(χ j (z,v)*S.euclideanHot (E.indices (φ n)) (z,v)))-
        (∫ v, ψ i v*(χ i (z,v)*E.hotLimit (EuclideanFlight.hotChart (z,v))))*
          (∫ v, ψ j v*(χ j (z,v)*E.hotLimit (EuclideanFlight.hotChart (z,v))))) 1
          (volume.restrict D)) atTop (𝓝 0) := by
  obtain ⟨φ,hφ,hconv⟩ := E.global_strong_averages hcarleman hGLPS S hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ χ hχ hc hs ψ hψ hψc
  choose a A R ha haA hA hwin using fun j =>
    exists_positive_cutoff_window E.horizon_ge (hc j) (hs j)
  have hbound j := S.eventually_hot_average_bounded hs₀ hsmax hη hηmax hK hd₀.le hq₂
    E.horizon_limit (ha j).le (haA j) (hA j) (hχ j).continuous (hc j) (hwin j)
    (hψ j).continuous (hψc j)
  choose B hB hb using hbound
  let f : ℕ → ℕ → Published.SpaceTime → ℝ := fun j n z =>
    ∫ v, ψ j v*(χ j (z,v)*S.euclideanHot (E.indices (φ n)) (z,v))
  let g : ℕ → Published.SpaceTime → ℝ := fun j z =>
    ∫ v, ψ j v*(χ j (z,v)*E.hotLimit (EuclideanFlight.hotChart (z,v)))
  have hfm j n : Measurable (f j n) := by
    have hm : Measurable (fun z : Published.KineticPhase =>
        ψ j z.2*(χ j z*S.euclideanHot (E.indices (φ n)) z)) :=
      ((hψ j).continuous.measurable.comp measurable_snd).mul
      ((hχ j).continuous.measurable.mul
        (S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨φ,hφ,fun i j D hD => ?_⟩
  have : IsFiniteMeasure ((volume : Measure Published.SpaceTime).restrict D) :=
    isFiniteMeasure_restrict.mpr hD.measure_lt_top.ne
  have hlocal k : Tendsto (fun n => eLpNorm (fun z => f k n z-g k z) 1 (volume.restrict D))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv k)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hlocalBound k : ∀ᶠ n in atTop, ∀ᵐ z ∂volume.restrict D, |f k n z| ≤ B k := by
    filter_upwards [hφ.tendsto_atTop.eventually (hb k)] with n hn
    exact ae_restrict_of_ae hn
  exact Compactness.tendsto_L1_product_of_eventually_bounded
    (fun n => (hfm i n).aestronglyMeasurable) (fun n => (hfm j n).aestronglyMeasurable)
    (hlocal i) (hlocal j) (hB i) (hlocalBound i) (hlocalBound j)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot pair limit has the factorized tensor moments -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.factorized_moments
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ) (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | 0 < z.1.1 ∧ ENNReal.ofReal z.1.1 < E.horizon})
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∀ i j (A R : ℝ), 0 ≤ A → ENNReal.ofReal A < E.horizon →
      ∀ D : Set Published.SpaceTime, IsCompact D → D ⊆ EuclideanFlight.hotBaseSet A R →
      (fun z => ∫ y : Velocity × Velocity,
        ((ψ i y.1*χ i (z,y.1))*(ψ j y.2*χ j (z,y.2)))*
          E.pairLimit (EuclideanFlight.hotPairChart (z,y))) =ᵐ[volume.restrict D]
      (fun z => (∫ v, ψ i v*(χ i (z,v)*E.toHotLimitExtraction.hotLimit
        (EuclideanFlight.hotChart (z,v))))*(∫ w, ψ j w*(χ j (z,w)*
          E.toHotLimitExtraction.hotLimit (EuclideanFlight.hotChart (z,w))))) := by
  obtain ⟨φ,hφ,hconv⟩ := E.toHotLimitExtraction.strong_average_products hcarleman hGLPS S
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ χ hχ hc hs ψ hψ hψc
  let E' := E.subsequence φ hφ
  have hhot : E'.toHotLimitExtraction.hotLimit = E.toHotLimitExtraction.hotLimit := rfl
  have hpair : E'.pairLimit = E.pairLimit := rfl
  have hind : E'.indices = E.indices ∘ φ := rfl
  let k : ℕ → Published.KineticPhase → ℝ := fun i z => ψ i z.2*χ i z
  have hk i : Continuous (k i) :=
    ((hψ i).continuous.comp continuous_snd).mul (hχ i).continuous
  have hkc i : HasCompactSupport (k i) := (hc i).mul_left
  intro i j A R hA0 hA D hD hDw
  have ht : Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, k i (z,v)*S.euclideanHot (E'.indices n) (z,v))*
        (∫ w, k j (z,w)*S.euclideanHot (E'.indices n) (z,w))-
      (∫ v, k i (z,v)*E'.toHotLimitExtraction.hotLimit (EuclideanFlight.hotChart (z,v)))*
        (∫ w, k j (z,w)*E'.toHotLimitExtraction.hotLimit (EuclideanFlight.hotChart (z,w)))) 1
        (volume.restrict D)) atTop (𝓝 0) := by
    simpa only [hind,hhot,Function.comp_apply,k,mul_assoc] using hconv i j D hD
  have he := E'.pair_moment_of_strong hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA0 hA
    (hk i) (hk j) (hkc i) (hkc j) hD hDw ht
  simpa only [hpair,hhot,k,mul_assoc] using he

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual weak hot pair limit is the pair product of the hot density -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.pairLimit_eq_product
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    (E.pairLimit ∘ EuclideanFlight.hotPairChart) =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume]
      CollisionCompactness.pairProduct (E.toHotLimitExtraction.hotLimit ∘ EuclideanFlight.hotChart) := by
  have : SFinite (EuclideanFlight.hotBaseVolume A R) := by
    unfold EuclideanFlight.hotBaseVolume
    infer_instance
  obtain ⟨ψ,hψ,hψc,hdet⟩ := Compactness.exists_countable_smooth_determining_tests
  choose β hβ hβc _hβn hβtest using fun i => Compactness.exists_velocity_cutoff (hψc i)
  obtain ⟨χ,hχ,hχc,hχs,hcover⟩ := Compactness.exists_spacetime_cutoff_cover
    (EuclideanFlight.hotRegion_open E.horizon) (EuclideanFlight.hotRegion_nonempty E.horizon_ge)
  let cuts : ℕ → Published.KineticPhase → ℝ := fun n =>
    Compactness.productCutoff (χ (Nat.unpair n).1) (β (Nat.unpair n).2)
  let tests : ℕ → Velocity → ℝ := fun n => ψ (Nat.unpair n).2
  have hcuts n : ContDiff ℝ (⊤ : ℕ∞) (cuts n) :=
    Compactness.productCutoff_smooth (hχ _) (hβ _)
  have hcutsc n : HasCompactSupport (cuts n) :=
    Compactness.productCutoff_compact (hχc _) (hβc _)
  have hcutss n : tsupport (cuts n) ⊆
      {z | 0 < z.1.1 ∧ ENNReal.ofReal z.1.1 < E.horizon} := by
    intro z hz
    exact hχs _ (Compactness.productCutoff_tsupport _ _ hz).1
  have hfmom := E.factorized_moments hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ cuts hcuts hcutsc hcutss tests
    (fun n => hψ _) (fun n => hψc _)
  have hw (s i : ℕ) (z : Published.KineticPhase) :
      tests (Nat.pair s i) z.2*cuts (Nat.pair s i) z = χ s z.1*ψ i z.2 := by
    dsimp only [cuts,tests]
    rw [Nat.unpair_pair]
    change ψ i z.2*(χ s z.1*β i z.2) = χ s z.1*ψ i z.2
    calc
      _ = χ s z.1*(ψ i z.2*β i z.2) := by ring
      _ = _ := by rw [hβtest]
  have hwf (s i : ℕ) (z : Published.KineticPhase) (u : ℝ) :
      tests (Nat.pair s i) z.2*(cuts (Nat.pair s i) z*u) = (χ s z.1*ψ i z.2)*u := by
    rw [← mul_assoc,hw]
  have hwv (s i : ℕ) (x : Published.SpaceTime) (v : Velocity) :
      tests (Nat.pair s i) v*cuts (Nat.pair s i) (x,v) = χ s x*ψ i v := hw s i (x,v)
  have hwfv (s i : ℕ) (x : Published.SpaceTime) (v : Velocity) (u : ℝ) :
      tests (Nat.pair s i) v*(cuts (Nat.pair s i) (x,v)*u) = (χ s x*ψ i v)*u := hwf s i (x,v) u
  let g := E.toHotLimitExtraction.hotLimit ∘ EuclideanFlight.hotChart
  let W := E.pairLimit ∘ EuclideanFlight.hotPairChart
  have hg := E.toHotLimitExtraction.euclidean_weak S hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA R
  have hW := E.euclidean_pair_weak hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA R
  have hscaled (s i j : ℕ) : ∀ᵐ x ∂EuclideanFlight.hotBaseVolume A R,
      (∫ y : Velocity × Velocity, ((χ s x*ψ i y.1)*(χ s x*ψ j y.2))*W (x,y)) =
        (∫ v, (χ s x*ψ i v)*g (x,v))*(∫ w, (χ s x*ψ j w)*g (x,w)) := by
    apply Compactness.ae_of_all_compact_restrict
    intro D hD
    have hDc : IsCompact (D ∩ EuclideanFlight.hotBaseSet A R) :=
      hD.inter_right (EuclideanFlight.hotBaseSet_closed A R)
    have ht := hfmom (Nat.pair s i) (Nat.pair s j) A R hA0 hA
      (D ∩ EuclideanFlight.hotBaseSet A R) hDc inter_subset_right
    rw [EuclideanFlight.hotBaseVolume_eq,Measure.restrict_restrict hD.measurableSet]
    filter_upwards [ht] with x hx
    simpa only [hwv,hwfv,g,W,Function.comp_apply] using hx
  have hpatch s : ∀ᵐ x ∂EuclideanFlight.hotBaseVolume A R, χ s x ≠ 0 →
      (fun y => W (x,y)) =ᵐ[volume] (fun y : Velocity × Velocity => g (x,y.1)*g (x,y.2)) := by
    apply Compactness.pair_identity_on_patch hψ hψc hdet hW.1 hg.1 hW.2.1 hg.2.1 (χ s)
    exact fun i j => (hscaled s i j).mono (fun _ h _ => h)
  have hfib : ∀ᵐ x ∂EuclideanFlight.hotBaseVolume A R,
      (fun y => W (x,y)) =ᵐ[volume] (fun y : Velocity × Velocity => g (x,y.1)*g (x,y.2)) := by
    filter_upwards [ae_all_iff.mpr hpatch,EuclideanFlight.hotRegion_ae hA R] with x hx hxin
    obtain ⟨s,hs⟩ := hcover x hxin
    exact hx s hs
  exact (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun hW.1 (CollisionCompactness.pairProduct_measurable hg.1))).mpr hfib

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual normalized hot cap bound on each time trace -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHot_cap_at (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ}
    (ht : S.radius n*t ∈ Icc 0 (shrinkingHorizon F.horizonScale n)) :
    ∀ᵐ p : Velocity × Velocity, S.euclideanHot n ((t,p.1),p.2)/H q p.2 ≤ t+S.coldFraction n := by
  have hp := EuclideanFlight.phaseEquiv_measurePreserving.quasiMeasurePreserving.ae
    (S.rescaledHot_bound_at hs₀ hsmax hη hηmax hK hd₀ hq n ht)
  filter_upwards [hp] with p hp
  rw [S.euclideanHot_eq_rescaledHot]
  apply (div_le_iff₀ (H_pos q p.2)).mpr
  exact hp

theorem normalizedHot_cap_backward (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {a : ℝ}
    (ha : S.radius n*a ∈ Icc 0 (shrinkingHorizon F.horizonScale n)) (t : ℝ) :
    ∀ᵐ p : Velocity × Velocity,
      S.euclideanHot n (PositiveIteration.flight ((t,p.1),p.2) a)/H q p.2 ≤ a+S.coldFraction n := by
  have hp := (EuclideanFlight.flight_measurePreserving (a-t)).quasiMeasurePreserving.ae
    (S.normalizedHot_cap_at hs₀ hsmax hη hηmax hK hd₀ hq n ha)
  filter_upwards [hp] with p hp
  convert hp using 1
  unfold PositiveIteration.flight EuclideanFlight.flight
  congr 4
  module

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # An actual nonlinear weak hot limit on every bounded interior window -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.nonlinear_weak
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
      (fun n => CollisionCompactness.pairProduct (S.euclideanHot (E.indices n)))
      (CollisionCompactness.pairProduct
        (E.toHotLimitExtraction.hotLimit ∘ EuclideanFlight.hotChart)) := by
  exact (E.euclidean_pair_weak hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA R).congr_limit
    (CollisionCompactness.pairProduct_measurable
      (E.toHotLimitExtraction.hotLimit_measurable.comp EuclideanFlight.hotChart.measurable))
    (E.pairLimit_eq_product hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ hA0 hA R)

theorem exists_hot_nonlinear_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940HotWindows)
    (hDPpair : Published.DunfordPettis1940HotPairWindows) (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ E : HotPairExtraction S, ∀ A R : ℝ, 0 ≤ A → ENNReal.ofReal A < E.horizon →
      Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
        (fun n => CollisionCompactness.pairProduct (S.euclideanHot (E.indices n)))
        (CollisionCompactness.pairProduct
          (E.toHotLimitExtraction.hotLimit ∘ EuclideanFlight.hotChart)) := by
  obtain ⟨E⟩ := S.exists_hot_limit_extraction hDP hs₀ hsmax hη hηmax hK hd₀.le hq₂
  obtain ⟨P⟩ := S.exists_hot_pair_limit hDPpair E hs₀ hsmax hη hηmax hK hd₀.le hq₂
  exact ⟨P,fun A R hA0 hA => P.nonlinear_weak hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hA0 hA R⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The hard-sphere weighted hot pair converges to the nonlinear limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.weighted_nonlinear_subsequence
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ A R : ℝ, 0 ≤ A → ENNReal.ofReal A < E.horizon →
      Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
        (fun n => CollisionCompactness.pairDensity (S.euclideanHot (E.indices (φ n))))
        (CollisionCompactness.pairDensity
          (E.toHotLimitExtraction.hotLimit ∘ EuclideanFlight.hotChart)) := by
  have hm n := CollisionCompactness.pairDensity_measurable
    (S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n))
  have hb (j : ℕ) := S.hotWeightedPair_bounds hs₀ hsmax hη hηmax hK hd₀.le hq₂
    (show 0 ≤ (j:ℝ)+1 by positivity) ((j:ℝ)+1)
  obtain ⟨φ,G,hφ,hG⟩ := Published.L1WeakCompactnessInput.countable
    (fun j : ℕ => hotPairWindowVolume (j+1) (j+1))
    (fun j => hDP (j+1) (j+1) (by positivity) (by positivity)) hm
    (fun j => Compactness.uniformIntegrable_comp (hb j).1 E.indices)
    (fun j => (hb j).2.comp E.indices)
  refine ⟨φ,hφ,fun A R hA0 hA => ?_⟩
  obtain ⟨j,hj⟩ := exists_nat_gt (max A R)
  have hAj : A ≤ (j:ℝ)+1 := by have := (le_max_left A R).trans_lt hj; linarith
  have hRj : R ≤ (j:ℝ)+1 := by have := (le_max_right A R).trans_lt hj; linarith
  have hGj := (hG j).restrict (hotPairWindowSet_measurable A R)
  rw [hotPairWindowVolume_restrict hAj hRj] at hGj
  have hweighted := S.weighted_pair_physical_weak hs₀ hsmax hη hηmax hK hd₀.le hq₂
    (E.horizon_limit.comp hφ.tendsto_atTop) hA hGj
  have hraw := (E.nonlinear_weak hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hA0 hA R).comp hφ.tendsto_atTop
  let w : Published.SpaceTime × (Velocity × Velocity) → ℝ :=
    fun z => 1+‖z.2.1‖+‖z.2.2‖
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hw1 (z) : 1 ≤ w z := by
    dsimp [w]
    linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
  have heq (u : Published.KineticPhase → ℝ) :
      (fun z => w z*CollisionCompactness.pairProduct u z) =
        CollisionCompactness.pairDensity u := by
    funext z
    simp only [w,CollisionCompactness.pairProduct,CollisionCompactness.pairDensity,mul_assoc]
  have hw' : Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
      (fun n z => w z*CollisionCompactness.pairProduct
        (S.euclideanHot (E.indices (φ n))) z) (G j ∘ EuclideanFlight.hotPairChart) := by
    have hs : (fun n z => w z*CollisionCompactness.pairProduct
        (S.euclideanHot (E.indices (φ n))) z) =
        (fun n => CollisionCompactness.pairDensity (S.euclideanHot (E.indices (φ n)))) :=
      funext (fun n => heq _)
    rw [hs]
    exact hweighted
  have hlim := Published.identify_weighted_weak_limit hraw hw' hw hw1
  rw [heq] at hlim
  exact hweighted.congr_limit
    (CollisionCompactness.pairDensity_measurable
      (E.toHotLimitExtraction.hotLimit_measurable.comp EuclideanFlight.hotChart.measurable)) hlim

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The identified hot pair in the physical capped representative -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.pairLimit_eq_capped_product
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    E.pairLimit =ᵐ[hotPairWindowVolume A R]
      CollisionCompactness.pairProduct E.toHotLimitExtraction.cappedHot := by
  have he := E.pairLimit_eq_product hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hA0 hA R
  have hp := (MeasurePreserving.symm EuclideanFlight.hotPairChart
    (EuclideanFlight.hotPairChart_measurePreserving A R)).quasiMeasurePreserving.ae he
  have hraw : E.pairLimit =ᵐ[hotPairWindowVolume A R]
      CollisionCompactness.pairProduct E.toHotLimitExtraction.hotLimit := by
    filter_upwards [hp] with z hz
    simp only [Function.comp_apply,MeasurableEquiv.apply_symm_apply] at hz
    change E.pairLimit z = E.toHotLimitExtraction.hotLimit
      ((z.1.1,EuclideanFlight.spaceEquiv (EuclideanFlight.spaceEquiv.symm z.1.2)),z.2.1)*
      E.toHotLimitExtraction.hotLimit
      ((z.1.1,EuclideanFlight.spaceEquiv (EuclideanFlight.spaceEquiv.symm z.1.2)),z.2.2) at hz
    simpa only [MeasurableEquiv.apply_symm_apply,CollisionCompactness.pairProduct,Prod.mk.eta] using hz
  have : SFinite (hotBaseWindowVolume A R) := by unfold hotBaseWindowVolume; infer_instance
  exact hraw.trans (CollisionCompactness.pairProduct_congr
    E.toHotLimitExtraction.hotLimit_measurable E.toHotLimitExtraction.cappedHot_measurable
    (E.toHotLimitExtraction.cappedHot_eq A R).symm)

theorem HotPairExtraction.capped_pair_weak
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges (hotPairWindowVolume A R)
      (fun n => CollisionCompactness.pairProduct (S.hotDensity (E.indices n)))
      (CollisionCompactness.pairProduct E.toHotLimitExtraction.cappedHot) :=
  (E.pairLimit_weak A R).congr_limit
    (CollisionCompactness.pairProduct_measurable E.toHotLimitExtraction.cappedHot_measurable)
    (E.pairLimit_eq_capped_product hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ hA0 hA R)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Every bounded measurable hot average converges strongly on the same sequence -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.strong_all_hot_averages
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, ψ v*S.hotDensity (E.indices n) (x,v))-
      (∫ v, ψ v*E.toHotLimitExtraction.cappedHot (x,v))) 1 (hotBaseWindowVolume A R))
      atTop (𝓝 0) := by
  let μ := hotBaseWindowVolume A R
  let _ : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  have : IsFiniteMeasure μ := by dsimp [μ,hotBaseWindowVolume]; infer_instance
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  let C := (B*(A+1))*(∫ v, H q v)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hB (by linarith)) (integral_nonneg (H_nonneg q))
  have hw := (E.toHotLimitExtraction.hotLimit_weak A R).congr_limit
    E.toHotLimitExtraction.cappedHot_measurable (E.toHotLimitExtraction.cappedHot_eq A R).symm
  have hp := E.capped_pair_weak hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hA0 hA R
  have hi (n) : Integrable (S.hotDensity (E.indices n)) (μ.prod volume) :=
    memLp_one_iff_integrable.mp ((S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀.le hq₂ A R).memLp _)
  have hpi (n) : Integrable (CollisionCompactness.pairProduct (S.hotDensity (E.indices n)))
      (μ.prod (volume : Measure (Velocity × Velocity))) :=
    memLp_one_iff_integrable.mp ((S.hotPair_bounds hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA0 R).1.memLp _)
  have havg (n) : ∀ᵐ x ∂μ, |∫ v, ψ v*S.hotDensity (E.indices n) (x,v)| ≤ C := by
    filter_upwards [Measure.ae_ae_of_ae_prod
      (S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n) A R)] with x hx
    have hb := norm_integral_le_of_norm_le
      (f := fun v => ψ v*S.hotDensity (E.indices n) (x,v))
      ((integrable_H hq₂).const_mul (B*(A+1))) ?_
    · simpa only [Real.norm_eq_abs,integral_const_mul,C] using hb
    · filter_upwards [hx] with v hv
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
        (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq₂ _ _)]
      exact (mul_le_mul (hψB v) hv
        (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq₂ _ _) hB).trans_eq (by ring)
  have hlim : ∀ᵐ x ∂μ, |∫ v, ψ v*E.toHotLimitExtraction.cappedHot (x,v)| ≤ C := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with x hx
    have hb := norm_integral_le_of_norm_le
      (f := fun v => ψ v*E.toHotLimitExtraction.cappedHot (x,v))
      ((integrable_H hq₂).const_mul (B*(A+1))) ?_
    · simpa only [Real.norm_eq_abs,integral_const_mul,C] using hb
    · filter_upwards [] with v
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (E.toHotLimitExtraction.cappedHot_nonneg _)]
      have htx : x.1+E.fraction ≤ A+1 := by linarith [hx.2,E.fraction_mem.2]
      have hc := (E.toHotLimitExtraction.cappedHot_le hx.1 x.2 v).trans
        (mul_le_mul_of_nonneg_right htx (H_nonneg q v))
      exact (mul_le_mul (hψB v) hc (E.toHotLimitExtraction.cappedHot_nonneg _) hB).trans_eq (by ring)
  change Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity))) _ _ at hp
  rw [Measure.volume_eq_prod Velocity Velocity] at hp hpi
  exact Compactness.strong_average_of_weak_pairs hw hp
    (fun n => S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _)
    (Eventually.of_forall hi) (Eventually.of_forall hpi) hψ hψB hC
    (Eventually.of_forall havg) hlim

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak gain and loss limits for the actual rescaled hot density -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem euclideanHot_nonneg (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : Published.KineticPhase) :
    0 ≤ S.euclideanHot n z := by
  rw [euclideanHot_eq_chart]
  exact S.rescaledHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _

theorem HotPairExtraction.collision_subsequence
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ A R : ℝ, 0 ≤ A → ENNReal.ofReal A < E.horizon →
      Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
        (fun n => CollisionCompactness.gainDensity (S.euclideanHot (E.indices (φ n))))
        (CollisionCompactness.gainDensity
          (E.toHotLimitExtraction.hotLimit ∘ EuclideanFlight.hotChart)) ∧
      Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
        (fun n => CollisionCompactness.lossDensity (S.euclideanHot (E.indices (φ n))))
        (CollisionCompactness.lossDensity
          (E.toHotLimitExtraction.hotLimit ∘ EuclideanFlight.hotChart)) := by
  obtain ⟨φ,hφ,hweighted⟩ := E.weighted_nonlinear_subsequence hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨φ,hφ,fun A R hA0 hA => ?_⟩
  have : SFinite (EuclideanFlight.hotBaseVolume A R) := by
    unfold EuclideanFlight.hotBaseVolume
    infer_instance
  have hi := (E.toHotLimitExtraction.subsequence φ hφ).eventually_weighted_pair_integrable
    hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA0 hA R
  exact CollisionCompactness.weak_gainLoss_eventually
    (fun n => S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _)
    (fun n => S.euclideanHot_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq₂ _)
    (E.toHotLimitExtraction.hotLimit_measurable.comp EuclideanFlight.hotChart.measurable)
    (hweighted A R hA0 hA) hi

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual rescaled hot-hot error vanishes on each interior window -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.vanishing_quadratic_subsequence
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ A R : ℝ, 0 ≤ A → ENNReal.ofReal A < E.horizon →
      Tendsto (fun n => eLpNorm (fun z => (S.radius (E.indices (φ n)))^2 *
        CollisionCompactness.collisionSource (F.indices (E.indices (φ n))+1)
          (S.euclideanHot (E.indices (φ n))) z) 1
        ((EuclideanFlight.hotBaseVolume A R).prod volume)) atTop (𝓝 0) := by
  obtain ⟨φ,hφ,hcollision⟩ := E.collision_subsequence hDP hcarleman hGLPS hs₀ hsmax
    hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨φ,hφ,fun A R hA0 hA => ?_⟩
  have : SFinite (EuclideanFlight.hotBaseVolume A R) := by
    unfold EuclideanFlight.hotBaseVolume
    infer_instance
  have hi := (E.toHotLimitExtraction.subsequence φ hφ).eventually_weighted_pair_integrable
    hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA0 hA R
  have hr : Tendsto (fun n => (S.radius (E.indices (φ n)))^2) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
      ((S.radius_tendsto_zero hs₀).comp (E.indices_strict.comp hφ).tendsto_atTop).pow 2
  exact CollisionCompactness.vanishing_cutoff_collision
    (fun n => S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _)
    (fun n => S.euclideanHot_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq₂ _)
    hi (hcollision A R hA0 hA).1 (hcollision A R hA0 hA).2 _ hr

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Integrability of the actual hot density and source on physical cylinders -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_physicalHot_cylinder_integrable (S : AttainedCapSequence F)
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {a A : ℝ} (ha : 0 ≤ a)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    ∀ᶠ n in atTop, Integrable (S.physicalHotDensity (E.indices n))
      ((coldCylinderVolume a A R).prod volume) := by
  have hui := S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀ hq A R
  filter_upwards [S.eventually_extendedHot_eq hs₀ E.horizon_limit hA] with n hn
  have hi : Integrable (S.hotDensity (E.indices n)) (hotWindowVolume A R) :=
    memLp_one_iff_integrable.mp (hui.memLp (E.indices n))
  have he : S.hotDensity (E.indices n) =ᵐ[hotWindowVolume A R]
      S.physicalHotDensity (E.indices n) := by
    filter_upwards [hotWindow_time_mem A R] with z hz
    exact hn z.1.1 hz (z.1.2,z.2)
  rw [coldCylinderVolume_eq_hot_restrict ha]
  exact (hi.congr he).mono_measure Measure.restrict_le_self

theorem eventually_hotSource_cylinder_integrable (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) (R : ℝ) :
    ∀ᶠ n in atTop, Integrable (S.hotSourceDensity a A (κ n))
      ((coldCylinderVolume a A R).prod volume) := by
  filter_upwards [S.eventually_hotSourceDensity_bound hcarleman hs₀ hsmax hη hηmax hK
    hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA R] with n hn
  have hi : Integrable (S.hotSourceDensity a A (κ n)) (hotWindowVolume A R) := by
    apply (sourceEnvelope_window_integrable hq₂ s₀ η K α γ d₀ a A R).mono'
      (S.hotSourceDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ a A _).aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hn
  rw [coldCylinderVolume_eq_hot_restrict ha.le]
  exact hi.mono_measure Measure.restrict_le_self

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Both error terms in the dilated hot equation vanish locally -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.vanishing_collision_error
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a A R : ℝ, 0 < a → a ≤ A →
      ENNReal.ofReal A < E.horizon →
      Tendsto (fun n => eLpNorm (fun z => (S.radius (E.indices (φ n)))^2 *
        CollisionCompactness.collisionSource (F.indices (E.indices (φ n))+1)
          (S.euclideanHot (E.indices (φ n))) z+
        S.coldSourceDensity a A (E.indices (φ n)) (EuclideanFlight.hotChart z)) 1
        ((EuclideanFlight.hotBaseVolume A R).prod volume)) atTop (𝓝 0) := by
  obtain ⟨φ,hφ,hquad⟩ := E.vanishing_quadratic_subsequence hDP hcarleman hGLPS hs₀ hsmax
    hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨φ,hφ,fun a A R ha haA hA => ?_⟩
  have hc := S.coldSourceDensity_tendsto_zero hcarleman hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq₁ hq₂ (E.indices_strict.comp hφ)
    (E.horizon_limit.comp hφ.tendsto_atTop) ha haA hA R
  have he (n) : eLpNorm (fun z =>
      S.coldSourceDensity a A (E.indices (φ n)) (EuclideanFlight.hotChart z)) 1
        ((EuclideanFlight.hotBaseVolume A R).prod volume) =
      eLpNorm (S.coldSourceDensity a A (E.indices (φ n))) 1 (hotWindowVolume A R) := by
    exact eLpNorm_comp_measurePreserving
      (S.coldSourceDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ a A _).aestronglyMeasurable
      (EuclideanFlight.hotChart_measurePreserving A R)
  have hc' : Tendsto (fun n => eLpNorm (fun z =>
      S.coldSourceDensity a A (E.indices (φ n)) (EuclideanFlight.hotChart z)) 1
        ((EuclideanFlight.hotBaseVolume A R).prod volume)) atTop (𝓝 0) := by
    simpa only [he,Function.comp_def] using hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (hquad A R (ha.le.trans haA) hA).add hc')
    (fun _ => bot_le) (fun _ => ?_)
  exact eLpNorm_add_le (by norm_num)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A zero cap limit makes the actual bounded iteration input locally small -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_euclidean_L1 (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A R : ℝ}
    (hA : ENNReal.ofReal A < E.horizon)
    (hz : (E.hotLimit ∘ EuclideanFlight.hotChart) =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0) :
    Tendsto (fun n => eLpNorm (S.euclideanHot (E.indices n)) 1
      ((EuclideanFlight.hotBaseVolume A R).prod volume)) atTop (𝓝 0) := by
  apply (E.euclidean_weak S hs₀ hsmax hη hηmax hK hd₀ hq hA R).nonnegative_zero_L1 hz
    (S.eventually_euclideanHot_integrable E hs₀ hsmax hη hηmax hK hd₀ hq hA R)
  exact Eventually.of_forall (fun n => ae_of_all _
    (S.euclideanHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n)))

theorem HotLimitExtraction.zero_boundedHotRatio_L1 (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A R V : ℝ}
    (hA : ENNReal.ofReal A < E.horizon) (hV : 0 ≤ V)
    (hz : (E.hotLimit ∘ EuclideanFlight.hotChart) =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0) :
    Tendsto (fun n => eLpNorm (S.boundedHotRatio (E.indices n)) 1
      (((EuclideanFlight.hotBaseVolume A R).prod volume).restrict {z | ‖z.2‖ ≤ V})) atTop (𝓝 0) := by
  have hratio := Compactness.tendsto_L1_div_H_on_velocity_ball
    (fun n => S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n))
    (E.zero_euclidean_L1 hs₀ hsmax hη hηmax hK hd₀ hq hA hz) q hV
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
    (fun _ => bot_le)
  intro n
  apply eLpNorm_mono_ae
    (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀ hq
      (E.indices n)).aestronglyMeasurable
  apply ae_of_all
  intro z
  have hn := div_nonneg (S.euclideanHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n) z)
    (H_nonneg q z.2)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (S.boundedHotRatio_bounds (E.indices n) z).1,abs_of_nonneg hn]
  exact max_le hn (min_le_right _ _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A zero cap limit forces local L1 smallness of the actual hot solutions -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_physical_L1 (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {a A R : ℝ} (ha : 0 ≤ a)
    (hA : ENNReal.ofReal A < E.horizon)
    (hz : E.hotLimit =ᵐ[(coldCylinderVolume a A R).prod volume] 0) :
    Tendsto (fun n => eLpNorm (S.physicalHotDensity (E.indices n)) 1
      ((coldCylinderVolume a A R).prod volume)) atTop (𝓝 0) := by
  apply (E.physical_weak_cylinder S hs₀ ha hA R).nonnegative_zero_L1 hz
    (S.eventually_physicalHot_cylinder_integrable E hs₀ hsmax hη hηmax hK hd₀ hq ha hA R)
  exact Eventually.of_forall (fun n => ae_of_all _ (fun z =>
    S.rescaledHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n) (z.1.1,(z.1.2,z.2))))

theorem HotLimitExtraction.zero_physical_inMeasure (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {a A R : ℝ} (ha : 0 ≤ a)
    (hA : ENNReal.ofReal A < E.horizon)
    (hz : E.hotLimit =ᵐ[(coldCylinderVolume a A R).prod volume] 0) :
    TendstoInMeasure ((coldCylinderVolume a A R).prod volume)
      (fun n => S.physicalHotDensity (E.indices n)) atTop 0 := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  simpa only [sub_zero] using E.zero_physical_L1 hs₀ hsmax hη hηmax hK hd₀ hq ha hA hz

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Local vanishing of the normalized hot ratio under a zero cap limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_ratio_L1 (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {a A R V : ℝ} (ha : 0 ≤ a)
    (hA : ENNReal.ofReal A < E.horizon) (hV : 0 ≤ V)
    (hz : E.hotLimit =ᵐ[(coldCylinderVolume a A R).prod volume] 0) :
    Tendsto (fun n => eLpNorm
      (fun z => S.physicalHotDensity (E.indices n) z / VelocityWeight.H q z.2) 1
      (((coldCylinderVolume a A R).prod volume).restrict {z | ‖z.2‖ ≤ V})) atTop (𝓝 0) :=
  Compactness.tendsto_L1_div_H_on_velocity_ball
    (fun _ => S.physicalHotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq _)
    (E.zero_physical_L1 hs₀ hsmax hη hηmax hK hd₀ hq ha hA hz) q hV

theorem HotLimitExtraction.zero_ratio_inMeasure (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {a A R V : ℝ} (ha : 0 ≤ a)
    (hA : ENNReal.ofReal A < E.horizon) (hV : 0 ≤ V)
    (hz : E.hotLimit =ᵐ[(coldCylinderVolume a A R).prod volume] 0) :
    TendstoInMeasure (((coldCylinderVolume a A R).prod volume).restrict {z | ‖z.2‖ ≤ V})
      (fun n z => S.physicalHotDensity (E.indices n) z / VelocityWeight.H q z.2) atTop 0 := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  simpa only [sub_zero] using E.zero_ratio_L1 hs₀ hsmax hη hηmax hK hd₀ hq ha hA hV hz

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
