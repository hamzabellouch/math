import OAI.MathematicalPhysics.Boltzmann.Approximation.SubcapCapLocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Approximation.SubcapMildLimits
import OAI.MathematicalPhysics.Boltzmann.Approximation.SubcapColdControl
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSliceIntegration
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeSurvival
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdCentralVanishing
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFiniteCap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

section

/-! # Actual zero-hot approximations with a uniform quadratic remainder -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState
namespace BoltzmannNonuniqueness.JetCopyDatum

/-- A uniform interval and actual zero-seed solutions, retaining the quadratic
hot estimate needed in the small-time separation argument. -/
theorem exists_dormant_approximation_family (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1/32 ∧
      ∃ F : ∀ N, BelowCap.Approximation s₀ η K α γ d₀ q T N,
        (∀ N, (F N).coefficient = 0) ∧
        ∀ N t, t ∈ Icc 0 T → PhaseEssSup.size (fun p => (F N).solution.value (t,p)-
          ∑' i, rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) (F N).amplitude)
            T N (F N).solution.value i (t,p)) ≤ t^2 := by
  obtain ⟨T,hT,hTmax,hzero⟩ := exists_uniform_zero_solution hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  have hex (N : ℕ) : ∃ F : BelowCap.Approximation s₀ η K α γ d₀ q T N,
      F.coefficient = 0 ∧ ∀ t ∈ Icc 0 T,
      PhaseEssSup.size (fun p => F.solution.value (t,p)-
        ∑' i, rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude)
          T N F.solution.value i (t,p)) ≤ t^2 := by
    let A := continuationAmplitude s₀ η K α d₀ N
    have hA : 0 < A := by
      have hp := WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N
      have hc := coldNormBound_nonneg hs₀ hK hd₀ η α N
      dsimp [A,continuationAmplitude]
      linarith
    have hz := hzero N (N+1) (by positivity)
    have he : (fun _ : JetPrototype.Phase => (0:ℝ)) =
        (fun p => (0:ℝ)*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) := by
      funext p
      simp
    rw [he] at hz
    obtain ⟨G,hG⟩ := hz
    have hi (p) : initial s₀ η K α γ d₀ q N
        (fun p => (0:ℝ)*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*A := by
      have hb := (seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα.le hαmax γ q N p).2
      have hc := coldNormBound_nonneg hs₀ hK hd₀ η α N
      simp only [initial,zero_mul,add_zero]
      have hamp := WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N
      dsimp [A,continuationAmplitude]
      linarith
    have hdom (s : Finset JetLattice.Label) (p) :
        ∑ i ∈ s, color s₀ η K α γ d₀ q N i p ≤
          initial s₀ η K α γ d₀ q N
            (fun p => (0:ℝ)*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p :=
      (initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N
        (fun p => by simp)).2 s p
    have hc (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
        color s₀ η K α γ d₀ q N i p ≤ 2*A := by
      refine ⟨color_nonneg hs₀ hK hd₀.le η α γ q N i p,?_⟩
      simpa only [Finset.sum_singleton] using (hdom {i} p).trans (hi p)
    have hreg := rebuilt_hot_continuous hq₂ (by positivity : (0:ℝ) ≤ N+1)
      (bounds (by positivity) hA).1 hT.le (by positivity : 0 ≤ 2*A) le_rfl G.measurable_value
      ((measurable_seed s₀ η K α γ d₀ q N).add
        ((HotSeedProfile.normalized_measurable q _).const_mul 0))
      (measurable_color s₀ η K α γ d₀ q N) G.value_bounds hi hc hdom (G.all_mild hT.le)
    have hpeak := Cap.peak_le_of_square hT.le (DatumBounds.scale_pos (η := η) hs₀ (N+1)) hreg hG
    let F : BelowCap.Approximation s₀ η K α γ d₀ q T N :=
      ⟨A,0,hA,⟨le_rfl,by norm_num⟩,hi,G,hpeak.trans (hTmax.trans (by norm_num))⟩
    exact ⟨F,rfl,hG⟩
  choose F hF hquad using hex
  exact ⟨T,hT,hTmax,F,hF,hquad⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Compact, tight zero-hot approximation families -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl
namespace BoltzmannNonuniqueness.JetCopyDatum

structure DormantFamily (s₀ η K α γ d₀ q : ℝ) extends BelowCap.TightFamily s₀ η K α γ d₀ q where
  coefficient_zero : ∀ N, (approximation N).coefficient = 0
  hot_quadratic : ∀ N t, t ∈ Icc 0 time →
    PhaseEssSup.size (fun p => (approximation N).solution.value (t,p)-
      ∑' i, rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) (approximation N).amplitude)
        time N (approximation N).solution.value i (t,p)) ≤ t^2

theorem exists_dormant_family (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) : Nonempty (DormantFamily s₀ η K α γ d₀ q) := by
  obtain ⟨T,hT,hTmax,F,hzero,hquad⟩ := exists_dormant_approximation_family hcarleman
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  have hαone : α ≤ 1 := hαmax.trans (by norm_num)
  have hc := BelowCap.cap_family_cutoff_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαone
    hγ hd₀ hd₀max hsmall hq₂ hT.le hTmax F
  let A : BelowCap.CompactFamily s₀ η K α γ d₀ q :=
    ⟨T,hT,hTmax,F,
      BelowCap.cap_family_density_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαone
        hγ hd₀ hd₀max hsmall hq₂ hT.le hTmax F,
      BelowCap.cap_family_pairs_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαone
        hγ hd₀ hd₀max hsmall hq₂ hT.le hTmax F,
      hc.1,hc.2,
      periodicInitial_L1_tendsto hs₀ hsmax hη hηmax hK hγ hd₀ (by linarith) hq₂ α
        (fun N => (F N).coefficient_mem)⟩
  have ht := BelowCap.cap_family_unifTight hs₀ hsmax hη hηmax hK hα hαone hγ hd₀ hd₀max
    hsmall hq₂ hT.le hTmax F
  let B : BelowCap.TightFamily s₀ η K α γ d₀ q := ⟨A,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2⟩
  exact ⟨⟨B,hzero,hquad⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # An admissible comparison solution from the actual zero-hot sequence -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl
namespace BoltzmannNonuniqueness.JetCopyDatum

structure DormantLimit {s₀ η K α γ d₀ q : ℝ} (A : DormantFamily s₀ η K α γ d₀ q) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  density : (ℝ × Position) × Velocity → ℝ
  weak_limit : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume A.time).prod volume)
    (fun n => torusPhysical q (A.approximation (subsequence n)).solution.value) density
  mild : MildCollisionSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density
  admissible : AdmissibleLocal A.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
    (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density)

theorem DormantFamily.exists_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : DormantFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    Nonempty (DormantLimit A) := by
  obtain ⟨φ,g,hφ,hg,S,hpair,htrace⟩ := A.toTightFamily.exists_mild_limit_with_traces_and_convergence
    hcarleman hGLPS hDP hs₀ hsmax hη hηmax hK.le hγ hd₀ hq₁ hq₂
  have hH := A.toTightFamily.entropy_mild_limit_of_convergence hcarleman hs₀ hsmax hη hηmax hK hγ hd₀
    hwidth hα.le hαmax hq₁ hq₂ hφ S hpair htrace
  have hdatum := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  obtain ⟨hfinite,hentropy⟩ := S.entropy_admissible A.time_pos hdatum hm hn hH
  have hbound := A.toCompactFamily.weak_limit_moment hs₀ hsmax hη hηmax hK.le hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ hg S.nonnegative
  have hbase := momentBase_nonneg hs₀ hK.le hd₀ η α q
  have hgain := JetEnvelopeGain.momentConstant_nonneg hK.le α γ
  have hE := CollisionCompactness.exponentialPair_integrable S.measurable S.nonnegative
    (fun u => AnnularEnvelope.commonMoment_nonneg hbase hgain s₀ η (AnnularEnvelope.torusChart u))
    (AnnularEnvelope.torus_common_square_integrable hs₀ hη hηmax A.time_pos.le
      (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)) hbound
  exact ⟨⟨φ,hφ,g,hg,S,S.localAdmissible A.time_pos hm hn hdatum hfinite hentropy hE⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The zero-hot remainder has an actual almost-everywhere quadratic bound -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem DormantFamily.hot_le {s₀ η K α γ d₀ q : ℝ}
    (A : DormantFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (A.approximation N).solution.value (t,p)-(A.approximation N).coldTotal (t,p) ≤ t^2 := by
  let F := A.approximation N
  have hc := F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq A.time_pos.le
  have hm : Measurable (fun p => F.solution.value (t,p)-F.coldTotal (t,p)) :=
    (F.solution.measurable_value.sub hc.1).comp (measurable_const.prodMk measurable_id)
  have hb (p) : |F.solution.value (t,p)-F.coldTotal (t,p)| ≤ 2*F.amplitude := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hc.2 (t,p)).2.2)]
    linarith [(hc.2 (t,p)).2.1,(F.solution.value_bounds (t,p)).2]
  have ha := PhaseEssSup.ae_abs_le_size hm hb
  have hsize : PhaseEssSup.size (fun p => F.solution.value (t,p)-F.coldTotal (t,p)) ≤ t^2 :=
    A.hot_quadratic N t ht
  filter_upwards [ha] with p hp
  exact (le_abs_self _).trans (hp.trans hsize)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A uniform physical majorant for the actual zero-hot family -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

def dormantMajorant (s₀ η K α d₀ q ε : ℝ) (z : Published.KineticPhase) : ℝ :=
  JetSupersolution.transverseDecayConstant K d₀ ε*‖transverse z.1.2‖^9+
    (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))*z.1.1^2*H q z.2

theorem dormantMajorant_measurable (s₀ η K α d₀ q ε : ℝ) :
    Measurable (dormantMajorant s₀ η K α d₀ q ε) := by
  unfold dormantMajorant
  exact ((measurable_const.mul ((ChartKernel.measurable_transverse.comp measurable_fst.snd).norm.pow_const 9))).add
    ((measurable_const.mul (measurable_fst.fst.pow_const 2)).mul ((ChartKernel.measurable_H q).comp measurable_snd))

theorem DormantFamily.central_bound {s₀ η K α γ d₀ q ε : ℝ}
    (A : DormantFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hε : 0 < ε) (N : ℕ) :
    ∀ᵐ u ∂(volume.restrict (Icc (0:ℝ) A.time)).prod (volume : Measure Velocity),
      ∀ᵐ v : Velocity, u.2 ∈ TorusChart.cube → ε ≤ ‖transverse v‖ →
        EuclideanFlight.density q (A.approximation N).solution.value (u,v) ≤
          dormantMajorant s₀ η K α d₀ q ε (u,v) := by
  let F := A.approximation N
  apply Compactness.ae_interval_nested_of_slices (T := A.time)
    (ν := (volume : Measure Velocity)) (ρ := (volume : Measure Velocity))
    (P := fun z : Published.KineticPhase => z.1.2 ∈ TorusChart.cube → ε ≤ ‖transverse z.2‖ →
      EuclideanFlight.density q F.solution.value z ≤ dormantMajorant s₀ η K α d₀ q ε z)
  · have hs : MeasurableSet {z : Published.KineticPhase | z.1.2 ∈ TorusChart.cube ∧ ε ≤ ‖transverse z.2‖} :=
      (TorusChart.measurableSet_cube.preimage measurable_fst.snd).inter
        (measurableSet_le measurable_const ((ChartKernel.measurable_transverse.comp measurable_snd).norm))
    have hl := measurableSet_le (EuclideanFlight.density_measurable F.solution.measurable_value q)
      (dormantMajorant_measurable s₀ η K α d₀ q ε)
    convert hs.compl.union hl using 1
    ext z
    simp only [mem_union,mem_compl_iff,mem_ofPred_eq,not_and_or,not_le,imp_iff_not_or,or_assoc]
  · intro t ht
    have ha := EuclideanFlight.phaseEquiv_measurePreserving.quasiMeasurePreserving.ae
      (A.hot_le hs₀ hsmax hη hηmax hK hd₀.le hq N ⟨ht.1.le,ht.2⟩)
    rw [Measure.volume_eq_prod] at ha
    filter_upwards [Measure.ae_ae_of_ae_prod ha] with x hx
    filter_upwards [hx] with v hv hxc hvc
    have hc := F.cold_central_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq A.time_pos.le A.time_le hε ht hxc hvc
    simp only [EuclideanFlight.phaseEquiv_apply,JetPeriodicDatum.phaseMap] at hv
    have hh := mul_le_mul_of_nonneg_left hv (H_nonneg q v)
    simp only [EuclideanFlight.density,PhysicalLocalization.density,
      EuclideanFlight.phaseEquiv_apply,JetPeriodicDatum.phaseMap]
    unfold dormantMajorant
    rw [Real.rpow_two] at hc
    nlinarith only [hc,hh]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact small-time scaling of the dormant majorant -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

def kineticDilation (r : ℝ) (z : Published.KineticPhase) : Published.KineticPhase :=
  ((r*z.1.1,r • z.1.2),z.2)

theorem kineticDilation_quasiMeasurePreserving {r : ℝ} (hr : 0 < r) :
    QuasiMeasurePreserving (kineticDilation r) volume volume := by
  have ht : QuasiMeasurePreserving (fun t : ℝ => r*t) volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr.ne'
  have hx : QuasiMeasurePreserving (fun x : Velocity => r • x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr.ne'
  have hv : QuasiMeasurePreserving (fun v : Velocity => v) volume volume :=
    (MeasurePreserving.id volume).quasiMeasurePreserving
  have htx : QuasiMeasurePreserving (Prod.map (fun t : ℝ => r*t) (fun x : Velocity => r • x))
      ((volume : Measure ℝ).prod (volume : Measure Velocity))
      ((volume : Measure ℝ).prod (volume : Measure Velocity)) := by
    refine ⟨by fun_prop,?_⟩
    rw [← Measure.map_prod_map _ _ ht.measurable hx.measurable]
    exact ht.absolutelyContinuous.prod hx.absolutelyContinuous
  have hp : QuasiMeasurePreserving
      (Prod.map (Prod.map (fun t : ℝ => r*t) (fun x : Velocity => r • x)) (fun v : Velocity => v))
      (((volume : Measure ℝ).prod (volume : Measure Velocity)).prod (volume : Measure Velocity))
      (((volume : Measure ℝ).prod (volume : Measure Velocity)).prod (volume : Measure Velocity)) := by
    refine ⟨by fun_prop,?_⟩
    rw [← Measure.map_prod_map _ _ htx.measurable hv.measurable]
    exact htx.absolutelyContinuous.prod hv.absolutelyContinuous
  have he : (Prod.map (Prod.map (fun t : ℝ => r*t) (fun x : Velocity => r • x))
      (fun v : Velocity => v)) = kineticDilation r := by
    funext z
    rfl
  rw [he] at hp
  simpa only [Measure.volume_eq_prod] using hp

theorem dormantMajorant_dilation {r : ℝ} (hr : 0 < r)
    (s₀ η K α d₀ q ε : ℝ) (z : Published.KineticPhase) :
    r⁻¹*dormantMajorant s₀ η K α d₀ q ε (kineticDilation r z) =
      JetSupersolution.transverseDecayConstant K d₀ ε*r^8*‖transverse z.1.2‖^9+
        (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))*r*z.1.1^2*H q z.2 := by
  have hs : transverse (r • z.1.2) = r • transverse z.1.2 := by
    ext i
    rfl
  unfold dormantMajorant kineticDilation
  rw [hs,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow]
  field_simp

theorem dormantMajorant_dilation_tendsto {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hlim : Filter.Tendsto r Filter.atTop (nhds 0))
    (s₀ η K α d₀ q ε : ℝ) (z : Published.KineticPhase) :
    Filter.Tendsto (fun n => (r n)⁻¹*dormantMajorant s₀ η K α d₀ q ε (kineticDilation (r n) z))
      Filter.atTop (nhds 0) := by
  simp_rw [dormantMajorant_dilation (hr _)]
  have h1 := ((hlim.pow 8).const_mul (JetSupersolution.transverseDecayConstant K d₀ ε)).mul_const
    (‖transverse z.1.2‖^9)
  have h2 := ((hlim.const_mul
    (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))).mul_const
      (z.1.1^2)).mul_const (H q z.2)
  simpa only [zero_pow (by norm_num : 8 ≠ 0),mul_zero,zero_mul,zero_add] using h1.add h2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The physical dormant majorant passes to the same admissible weak limit -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem DormantLimit.central_bound {s₀ η K α γ d₀ q ε : ℝ}
    {A : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit A)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hε : 0 < ε) :
    ∀ᵐ z ∂TorusKineticChart.cellVolume A.time, ε ≤ ‖transverse z.2‖ →
      TorusKineticChart.liftDensity D.density z ≤ dormantMajorant s₀ η K α d₀ q ε z := by
  let : SigmaFinite (TorusKineticChart.cellVolume A.time) := by
    unfold TorusKineticChart.cellVolume
    infer_instance
  have hw := TorusKineticChart.weak_density_transfer
    (fun n => (A.approximation (D.subsequence n)).solution.measurable_value) D.weak_limit
  let s : Set Published.KineticPhase := {z | ε ≤ ‖transverse z.2‖}
  have hs : MeasurableSet s :=
    measurableSet_le measurable_const ((ChartKernel.measurable_transverse.comp measurable_snd).norm)
  have hfi (n : ℕ) : Integrable
      (EuclideanFlight.density q (A.approximation (D.subsequence n)).solution.value)
      (TorusKineticChart.cellVolume A.time) :=
    memLp_one_iff_integrable.mp (A.toCompactFamily.density_ui_cell.memLp (D.subsequence n))
  apply hw.le_on_measurable hfi hs (dormantMajorant_measurable s₀ η K α d₀ q ε)
  intro n
  let f := EuclideanFlight.density q (A.approximation (D.subsequence n)).solution.value
  have hm : Measurable f := EuclideanFlight.density_measurable
    (A.approximation (D.subsequence n)).solution.measurable_value q
  have hP : MeasurableSet {z : Published.KineticPhase | z.1.2 ∈ TorusChart.cube →
      ε ≤ ‖transverse z.2‖ → f z ≤ dormantMajorant s₀ η K α d₀ q ε z} := by
    have hb := measurableSet_le hm (dormantMajorant_measurable s₀ η K α d₀ q ε)
    have hx := TorusChart.measurableSet_cube.preimage (measurable_fst.snd :
      Measurable (fun z : Published.KineticPhase => z.1.2))
    convert (hx.inter hs).compl.union hb using 1
    ext z
    simp only [mem_union,mem_compl_iff,mem_inter_iff,mem_preimage,mem_ofPred_eq,not_and_or,imp_iff_not_or,or_assoc,s]
  have hb := (Measure.ae_prod_iff_ae_ae hP).mpr
    (A.central_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq hε (D.subsequence n))
  have hle : TorusKineticChart.cellVolume A.time ≤
      ((volume.restrict (Icc (0:ℝ) A.time)).prod (volume : Measure Velocity)).prod
        (volume : Measure Velocity) :=
    Measure.prod_mono (Measure.prod_mono le_rfl Measure.restrict_le_self) le_rfl
  have hx : ∀ᵐ z ∂TorusKineticChart.cellVolume A.time, z.1.2 ∈ TorusChart.cube := by
    rw [TorusKineticChart.cellVolume_eq]
    filter_upwards [ae_restrict_mem (TorusKineticChart.measurableSet_region A.time)] with z hz
    exact hz.1.2
  filter_upwards [ae_mono hle hb,hx] with z hz hzx hzs
  exact hz hzx hzs

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The dormant weak limit retains its majorant after small-time dilation -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem DormantLimit.scaled_central_bound {s₀ η K α γ d₀ q ε r : ℝ}
    {A : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit A)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hε : 0 < ε) (hr : 0 < r) :
    ∀ᵐ z : Published.KineticPhase, r*z.1.1 ∈ Icc 0 A.time → r • z.1.2 ∈ TorusChart.cube →
      ε ≤ ‖transverse z.2‖ →
      r⁻¹*TorusKineticChart.liftDensity D.density (kineticDilation r z) ≤
        JetSupersolution.transverseDecayConstant K d₀ ε*r^8*‖transverse z.1.2‖^9+
          (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))*r*z.1.1^2*H q z.2 := by
  have hb := D.central_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq hε
  rw [TorusKineticChart.cellVolume_eq] at hb
  have hf := (ae_restrict_iff' (TorusKineticChart.measurableSet_region A.time)).mp hb
  filter_upwards [(kineticDilation_quasiMeasurePreserving hr).ae hf] with z hz ht hx hv
  have hreg : kineticDilation r z ∈ TorusKineticChart.region A.time := ⟨⟨ht,hx⟩,mem_univ _⟩
  have h := mul_le_mul_of_nonneg_left (hz hreg hv) (inv_nonneg.mpr hr.le)
  rwa [dormantMajorant_dilation hr] at h

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
