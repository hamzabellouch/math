import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundCappedLoss
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteDepthKernelOrder
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteHorizonRatio
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds
import OAI.MathematicalPhysics.Boltzmann.Jets.ThermalStripeIdentity

namespace OAI

section

/-! # Cold free-flight convergence without additional small-scale hypotheses -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_cold_dilation_limit {s₀ η K α γ d₀ q T a S U : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q T (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 T) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ x in Ω, ∫ v : Velocity,
      |r n*(H q v*(F n).cold (j n) (t n,(r n • x,v))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • x,v)))|
      ∂volume ∂JetPrototype.spaceVolume) atTop (𝓝 0) := by
  have hslim : Tendsto (fun n => jetScale s₀ η (j n).annulus) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (DatumBounds.scale_pos (η := η) hs₀ _).le) hhi
    simpa only [mul_zero] using hrlim.const_mul S
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (eventually_cold_survival_geometry (T := T) (d₀ := d₀) hη hslim)
  apply (tendsto_add_atTop_iff_nat n₀).mp
  exact cap_cold_dilation_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hT hTmax hq hsmall
    (fun n => N (n+n₀)) (fun n => F (n+n₀)) (fun n => j (n+n₀))
    (fun n => hj0 (n+n₀)) (fun n => hj (n+n₀)) (fun n => r (n+n₀)) (fun n => t (n+n₀))
    (fun n => hr (n+n₀)) (hrlim.comp (tendsto_add_atTop_nat n₀))
    (fun n => ht (n+n₀)) ha hS (fun n => hlo (n+n₀)) (fun n => hhi (n+n₀))
    (fun n => htime (n+n₀)) (fun n => hδ (n+n₀))
    (fun n => (hn₀ (n+n₀) (by omega)).1) (fun n => (hn₀ (n+n₀) (by omega)).2) Ω hΩ

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Local integrability of the actual cold colors and their free profiles -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.cold_physical_integrable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (i : JetLattice.Label) (t : ℝ) (μ : Measure JetPrototype.Space) [IsFiniteMeasure μ] :
    Integrable (fun p : JetPrototype.Phase => H q p.2*F.cold i (t,p)) (μ.prod volume) := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hm : Measurable (fun p : JetPrototype.Phase => H q p.2*F.cold i (t,p)) :=
    ((ChartKernel.measurable_H q).comp measurable_snd).mul
      ((hc.1 i).comp (measurable_const.prodMk measurable_id))
  apply (((integrable_H hq).comp_snd μ).const_mul (2*F.amplitude)).mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (mul_nonneg (H_nonneg q p.2) (hc.2.1 i (t,p)))]
  have hb : F.cold i (t,p) ≤ 2*F.amplitude := by
    simpa only [Finset.sum_singleton] using (hc.2.2.1 {i} (t,p)).trans (F.solution.value_bounds (t,p)).2
  exact (mul_le_mul_of_nonneg_left hb (H_nonneg q p.2)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.JetCopyDatum

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem local_integrable {K α γ s d t : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η : ℝ) (a : Bool)
    (μ : Measure JetPrototype.Space) [IsFiniteMeasure μ] :
    Integrable (free η K α γ s d t a) (μ.prod volume) := by
  have hi := JetBarrierLocalMass.local_integrable hK hα hγ hs hd ht htmax η a 0 μ
  simp only [sub_zero] at hi
  apply hi.mono' (measurable_free η K α γ s d t a).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (free_nonneg hK hs.le hd.le η α γ t a p)]
  exact free_le_barrier hK hd hα hγ hs ht (htmax.trans (by norm_num)) η a p

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # Product-space L1 convergence of the actual cold dilation to free transport -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_cold_L1_dilation_limit {s₀ η K α γ d₀ q T a S U : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q T (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 T) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ p : JetPrototype.Phase,
      |r n*(H q p.2*(F n).cold (j n) (t n,(r n • p.1,p.2))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • p.1,p.2)))|
      ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) := by
  have hbase := cap_cold_dilation_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hT hTmax hq hsmall N F j hj0 hj r t hr hrlim ht ha hS hlo hhi htime hδ Ω hΩ
  apply hbase.congr'
  have hslim : Tendsto (fun n => jetScale s₀ η (j n).annulus) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (DatumBounds.scale_pos (η := η) hs₀ _).le) hhi
    simpa only [mul_zero] using hrlim.const_mul S
  filter_upwards [eventually_cold_survival_geometry (T := T) (d₀ := d₀) hη hslim] with n hn
  have hcomp : IsCompact (r n • Ω) := hΩ.image (continuous_const_smul (r n))
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (r n • Ω)) :=
    isFiniteMeasure_restrict.mpr hcomp.measure_lt_top.ne
  have hb := (F n).local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hT hTmax hq hsmall 0 (j n) (hj0 n) (hj n) hn.1 hn.2 (r n • Ω) (ht n)
  dsimp only at hb
  exact (integral_prod _ (ColdDilationMeasure.integrable_dilated_error (hr n) Ω hb.1)).symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Bounded testing of the actual cold/free error -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelError (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  S.radius (E.indices n)*(H q p.2*(F.approximation (E.indices n)).cold (E.coldLabel k a n)
    (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2))-
    JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
      (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
      (S.radius (E.indices n)*t) a
      (shift (displacement (E.coldLabel k a n).lattice) (S.radius (E.indices n) • p.1,p.2)))

theorem HotLimitExtraction.coldLabelError_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (htmax : S.radius (E.indices n)*t ≤ 1)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Integrable (E.coldLabelError k a n t) ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  let r := S.radius (E.indices n)
  let i := E.coldLabel k a n
  let s := JetGeometry.jetScale s₀ η i.annulus
  let d := d₀*s^10
  let μ := JetPrototype.spaceVolume.restrict (r • Ω)
  have hr : 0 < r := S.radius_pos hs₀ (E.indices n)
  have hs : 0 < s := DatumBounds.scale_pos hs₀ _
  have hd : 0 < d := mul_pos hd₀ (pow_pos hs 10)
  let _ : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (hΩ.image (continuous_const_smul r)).measure_lt_top.ne
  have hc := (F.approximation (E.indices n)).cold_physical_integrable hs₀ hsmax hη hηmax hK hd₀.le hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le i (r*t) μ
  have hb := JetBarrierLocalMass.local_integrable hK hα hγ hs hd (mul_pos hr ht) htmax η a
    (displacement i.lattice) μ
  have hf : Integrable (fun p : JetPrototype.Phase => JetFreeTransport.free η K α γ s d (r*t) a
      (shift (displacement i.lattice) p)) (μ.prod volume) := by
    apply hb.mono' ((JetFreeTransport.measurable_free η K α γ s d (r*t) a).comp
      (measurable_shift _)).aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (JetFreeTransport.free_nonneg hK hs.le hd.le η α γ (r*t) a _)]
    exact JetFreeTransport.free_le_barrier hK hd hα hγ hs (mul_pos hr ht)
      (htmax.trans (by norm_num)) η a _
  exact (ColdDilationMeasure.integrable_dilate hr Ω (hc.sub hf)).const_mul r

theorem HotLimitExtraction.coldLabel_bounded_test_free_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {C : ℝ} (hC : 0 ≤ C) (φ : JetPrototype.Phase → ℝ) (hφ : ∀ p, |φ p| ≤ C) :
    Tendsto (fun n => ∫ p, φ p*E.coldLabelError k a n t p
      ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) := by
  have hl := E.coldLabel_free_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq
    k a hk ht htU Ω hΩ
  change Tendsto (fun n => ∫ p, |E.coldLabelError k a n t p|
    ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) at hl
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hl.const_mul C)
  filter_upwards [S.eventually_scaled_slab hs₀ E.horizon_limit htU] with n hn
  have htime : S.radius (E.indices n)*t ≤ 1 :=
    (hn t ⟨ht.le,le_rfl⟩).2.trans
      (((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le).trans (by norm_num))
  have hi := (E.coldLabelError_integrable hs₀ hsmax hη hηmax hK hα hγ hd₀ hq k a n ht htime Ω hΩ).abs
  have hb := norm_integral_le_of_norm_le (hi.const_mul C) (ae_of_all _ (fun p => by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hφ p) le_rfl (abs_nonneg _) hC))
  simpa only [integral_const_mul] using hb

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Annular mask replacement along the actual mesh-label sequence -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_mask_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ)
    (Ω : Set Transverse) (hΩ : volume Ω < ⊤) :
    let r := fun n => S.radius (E.indices n)
    let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
    let d := fun n => d₀*(s n)^10
    let μ := E.phase*Real.exp (η*(k:ℝ))
    Tendsto (fun n => ∫ p : Transverse × (Transverse × ℝ),
      |(JetGeometry.mask η (s n) a).indicator (fun _ => (1:ℝ))
          (r n • (p.1-t • (d n • p.2.1)))-
        (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1*
          (JetGeometry.stripe (s n) a).indicator (fun _ => (1:ℝ))
            (r n • (p.1-t • (d n • p.2.1)))| *
      JetThermalKernel.J (SheetMeasures.join p.2)
      ∂(volume.restrict Ω).prod ((volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
  intro r s d μ
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hb := JetGeometry.spatial_mask_L1_tendsto hr
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop)
    (E.coldLabel_scale_limit hs₀ hη k a) (E.coldLabel_width_tendsto_zero hs₀ hη k a)
    η t a Ω hΩ
  change Tendsto (fun n => ∫ p : Transverse × (Transverse × ℝ),
    |(JetGeometry.mask η (r n*(s n/r n)) a).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))-
      (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1*
        (JetGeometry.stripe (r n*(s n/r n)) a).indicator (fun _ => (1:ℝ))
          (r n • (p.1-t • (d n • p.2.1)))| *
    JetThermalKernel.J (SheetMeasures.join p.2)
    ∂(volume.restrict Ω).prod ((volume : Measure Transverse).prod volume)) atTop (𝓝 0) at hb
  simpa only [mul_div_cancel₀ _ (hr _).ne'] using hb

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Local L1 convergence of the cold/free velocity-average error -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_average_error_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => ∫ x, |∫ v, ψ v*E.coldLabelError k a n t (x,v)|
      ∂JetPrototype.spaceVolume.restrict Ω) atTop (𝓝 0) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hl := E.coldLabel_free_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq
    k a hk ht htU Ω hΩ
  change Tendsto (fun n => ∫ p, |E.coldLabelError k a n t p|
    ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) at hl
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
    _ (by simpa only [mul_zero] using hl.const_mul B)
  filter_upwards [S.eventually_scaled_slab hs₀ E.horizon_limit htU] with n hn
  have htime : S.radius (E.indices n)*t ≤ 1 :=
    (hn t ⟨ht.le,le_rfl⟩).2.trans
      (((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le).trans (by norm_num))
  have hi := E.coldLabelError_integrable hs₀ hsmax hη hηmax hK hα hγ hd₀ hq k a n ht htime Ω hΩ
  rw [← integral_const_mul,integral_prod _ (hi.abs.const_mul B)]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
    (hi.abs.const_mul B).integral_prod_left
  filter_upwards [hi.prod_right_ae] with x hx
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hx.abs.const_mul B)
  filter_upwards [] with v
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right (hψB v) (abs_nonneg _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The velocity averages of the actual retained cold colors -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelDensity (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  S.radius (E.indices n)*(H q p.2*(F.approximation (E.indices n)).cold (E.coldLabel k a n)
    (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2)))

def HotLimitExtraction.coldLabelAverage (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∫ v, ψ v*E.coldLabelDensity k a n t (x,v)

theorem HotLimitExtraction.coldLabelDensity_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Integrable (E.coldLabelDensity k a n t) ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  let r := S.radius (E.indices n)
  let μ := JetPrototype.spaceVolume.restrict (r • Ω)
  have hr : 0 < r := S.radius_pos hs₀ (E.indices n)
  let _ : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (hΩ.image (continuous_const_smul r)).measure_lt_top.ne
  have hi := (F.approximation (E.indices n)).cold_physical_integrable hs₀ hsmax hη hηmax
    hK hd₀ hq (shrinkingHorizon_pos F.horizonScale_pos _).le (E.coldLabel k a n) (r*t) μ
  exact (ColdDilationMeasure.integrable_dilate hr Ω hi).const_mul r

theorem HotLimitExtraction.coldLabelError_eq (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (p : JetPrototype.Phase) :
    E.coldLabelError k a n t p = E.coldLabelDensity k a n t p-
      S.radius (E.indices n)*JetFreeTransport.free η K α γ
        (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
        (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
        (S.radius (E.indices n)*t) a (S.radius (E.indices n) • p.1,p.2) := by
  have hz : displacement (E.coldLabel k a n).lattice = 0 := by
    change (JetLattice.transverseShift 0,JetLattice.axialShift 0) = 0
    ext i <;> simp [JetLattice.transverseShift,JetLattice.axialShift]
  unfold coldLabelError coldLabelDensity
  rw [hz]
  simp only [WeightedTranslation.shift,sub_zero]
  change _ = _
  ring

theorem HotLimitExtraction.coldLabelAverage_sub_free (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (htmax : S.radius (E.indices n)*t ≤ 1) (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᵐ x ∂JetPrototype.spaceVolume.restrict Ω,
      E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x =
        ∫ v, ψ v*E.coldLabelError k a n t (x,v) := by
  have hm := hψ.comp (measurable_snd : Measurable (Prod.snd : JetPrototype.Phase → Velocity))
  have hi := (E.coldLabelDensity_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k a n t Ω hΩ).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ (fun p => hψB p.2))
  have he := (E.coldLabelError_integrable hs₀ hsmax hη hηmax hK hα hγ hd₀ hq k a n ht htmax Ω hΩ).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ (fun p => hψB p.2))
  filter_upwards [hi.prod_right_ae,he.prod_right_ae] with x hix hex
  dsimp only [Function.comp_apply] at hix hex
  have hd : Integrable (fun v => S.radius (E.indices n)*JetFreeTransport.free η K α γ
      (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
      (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
      (S.radius (E.indices n)*t) a (S.radius (E.indices n) • x,v)*ψ v) := by
    apply (hix.sub hex).congr
    filter_upwards [] with v
    dsimp only [Pi.sub_apply]
    rw [E.coldLabelError_eq]
    ring
  have hident : (fun v => ψ v*E.coldLabelError k a n t (x,v)) =
      (fun v => ψ v*E.coldLabelDensity k a n t (x,v)-
        S.radius (E.indices n)*JetFreeTransport.free η K α γ
          (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
          (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
          (S.radius (E.indices n)*t) a (S.radius (E.indices n) • x,v)*ψ v) := by
    funext v
    rw [E.coldLabelError_eq]
    ring
  rw [hident,integral_sub hix hd]
  rfl

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Integrability of the actual, free and striped cold averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelStripeAverage_measurable (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) : Measurable (E.coldLabelStripeAverage k a n t) := by
  let r := S.radius (E.indices n)
  let s := JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  have hm : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (JetGeometry.stripe s a).indicator (fun _ => (1:ℝ))
        (r • (p.1-t • ((d₀*s^10) • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe s a)).comp (by fun_prop)
  exact (hm.mul ((JetThermalKernel.J_smooth.continuous.measurable.comp
    SheetMeasures.join.measurable).comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem HotLimitExtraction.coldLabelStripeAverage_bound (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (y : Transverse) :
    |E.coldLabelStripeAverage k a n t y| ≤ 1 := by
  apply JetCoreDensity.masked_thermal_bound
  intro w
  by_cases h : S.radius (E.indices n) •
      (y-t • ((d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10) • w.1)) ∈
      JetGeometry.stripe (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus) a
  · simp only [indicator_of_mem h,abs_one,le_refl]
  · simp only [indicator_of_notMem h,abs_zero,zero_le_one]

theorem HotLimitExtraction.coldLabelStripedProfile_measurable (E : HotLimitExtraction S)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (E.coldLabelStripedProfile k a n t ψ) := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  exact (JetCoreDensity.limitingCoefficient_measurable hα hγ hμ ht K (JetPrototype.sign a) hψ).mul
    (((measurable_const.indicator (JetGeometry.measurableSet_scaleShell η
      (E.phase*Real.exp (η*(k:ℝ))))).comp measurable_fst).mul
        ((E.coldLabelStripeAverage_measurable k a n t).comp measurable_fst))

theorem HotLimitExtraction.coldLabelStripedProfile_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : JetPrototype.Space) :
    |E.coldLabelStripedProfile k a n t ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hc := JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x
  have hs := E.coldLabelStripeAverage_bound k a n t x.1
  dsimp only [coldLabelStripedProfile]
  by_cases hx : x.1 ∈ JetGeometry.scaleShell η (E.phase*Real.exp (η*(k:ℝ)))
  · rw [indicator_of_mem hx,one_mul,abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans hc
  · rw [indicator_of_notMem hx,zero_mul,mul_zero,abs_zero]
    exact (abs_nonneg _).trans hc

theorem HotLimitExtraction.coldLabelStripedProfile_integrable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (E.coldLabelStripedProfile k a n t ψ) ρ :=
  Integrable.of_bound (E.coldLabelStripedProfile_measurable hα.le hγ.le k a n ht.le hψ).aestronglyMeasurable
    _ (ae_of_all _ (fun x => E.coldLabelStripedProfile_bound hK hα hγ k a n ht hψB x))

theorem HotLimitExtraction.coldLabelFreeAverage_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (E.coldLabelFreeAverage k a n t ψ) ρ := by
  have hs : 0 < JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus := DatumBounds.scale_pos hs₀ _
  apply Integrable.of_bound
    (JetCoreDensity.free_average_measurable _ _ _ _ _ _ _ _ _ hψ.measurable).aestronglyMeasurable
    (((K*max 1 (α*γ)⁻¹)/t)*B)
  exact ae_of_all _ (fun x => JetCoreDensity.dilated_free_average_bound (S.radius_pos hs₀ _) hK hα hγ
    hs (mul_pos hd₀ (pow_pos hs 10)) ht η a x hψ hψB)

theorem HotLimitExtraction.coldLabelAverage_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Integrable (E.coldLabelAverage k a n t ψ) (JetPrototype.spaceVolume.restrict Ω) := by
  have hi := (E.coldLabelDensity_integrable hs₀ hsmax hη hηmax hK hd₀ hq k a n t Ω hΩ).bdd_mul
    (hψ.comp measurable_snd).aestronglyMeasurable (ae_of_all _ (fun p => hψB p.2))
  exact hi.integral_prod_left

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual cold-label stripes average to one quarter -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelStripe_centered_eq (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (y : Transverse) :
    E.coldLabelStripeAverage k a n t y-1/4 =
      JetGeometry.thermalStripeCentered
        (S.radius (E.indices n)*
          (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus/S.radius (E.indices n))^2)
        (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10) t a y :=
  (JetGeometry.thermalStripeCentered_eq (S.radius_pos hs₀ _) _ _ _ _ _).symm

theorem HotLimitExtraction.coldLabelStripe_centered_weakStar (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ) :
    Compactness.WeakStarLInfConverges (volume : Measure Transverse)
      (fun n y => E.coldLabelStripeAverage k a n t y-1/4) (fun _ => 0) := by
  let r := fun n => S.radius (E.indices n)
  let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  have hr (n) : 0 < r n := S.radius_pos hs₀ _
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hp (n) : 0 < r n*(s n/r n)^2 := mul_pos (hr n) (pow_pos (div_pos (hs n) (hr n)) 2)
  have hplim := JetGeometry.stripe_period_tendsto_zero
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop)
    (E.coldLabel_scale_limit hs₀ hη k a)
  have h := JetGeometry.thermalStripeCentered_weakStar hp hplim
    (fun n => d₀*(s n)^10) t a
  have heq : (fun n y => E.coldLabelStripeAverage k a n t y-1/4) =
      (fun n => JetGeometry.thermalStripeCentered (r n*(s n/r n)^2) (d₀*(s n)^10) t a) := by
    funext n y
    exact E.coldLabelStripe_centered_eq hs₀ k a n t y
  rw [heq]
  exact h

theorem HotLimitExtraction.coldLabelStripe_weakStar (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ) :
    Compactness.WeakStarLInfConverges (volume : Measure Transverse)
      (fun n => E.coldLabelStripeAverage k a n t) (fun _ => 1/4) := by
  refine ⟨measurable_const,?_⟩
  intro ψ hψ
  have hi (n) : Integrable (fun y => ψ y*E.coldLabelStripeAverage k a n t y) :=
    (hψ.bdd_mul (E.coldLabelStripeAverage_measurable k a n t).aestronglyMeasurable
      (ae_of_all _ (E.coldLabelStripeAverage_bound k a n t))).congr
        (ae_of_all _ (fun y => mul_comm _ _))
  have heq (n) : (∫ y, ψ y*(E.coldLabelStripeAverage k a n t y-1/4)) =
      (∫ y, ψ y*E.coldLabelStripeAverage k a n t y)-(∫ y, ψ y*(1/4)) := by
    simp_rw [mul_sub]
    exact integral_sub (hi n) (hψ.mul_const (1/4))
  have h := (E.coldLabelStripe_centered_weakStar hs₀ hη k a t).2 ψ hψ
  simp only [mul_zero,integral_zero,heq] at h
  simpa only [zero_add,sub_add_cancel] using h.add_const (∫ y, ψ y*(1/4))

theorem HotLimitExtraction.coldLabelStripe_space_centered_weakStar (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ) :
    Compactness.WeakStarLInfConverges JetPrototype.spaceVolume
      (fun n x => E.coldLabelStripeAverage k a n t x.1-1/4) (fun _ => 0) := by
  apply Compactness.weakStar_zero_of_fibers
  · intro n
    exact ((E.coldLabelStripeAverage_measurable k a n t).comp measurable_fst).sub_const (1/4)
  · intro n x
    rw [E.coldLabelStripe_centered_eq hs₀]
    exact JetGeometry.thermalStripeCentered_bound _ _ _ _ _
  · intro _
    exact E.coldLabelStripe_centered_weakStar hs₀ hη k a t

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Every actual cold-label velocity fiber is integrable -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelDensity_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) :
    Measurable (E.coldLabelDensity k a n t) := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hp : Measurable (fun p : JetPrototype.Phase =>
      (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2))) := by fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).mul ((hc.1 _).comp hp)).const_mul _

theorem HotLimitExtraction.coldLabelDensity_bounds (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ)
    (p : JetPrototype.Phase) :
    0 ≤ E.coldLabelDensity k a n t p ∧ E.coldLabelDensity k a n t p ≤
      (S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude))*H q p.2 := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hb := (hc.2.2.1 {E.coldLabel k a n}
    (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2))).trans
      ((F.approximation (E.indices n)).solution.value_bounds _).2
  simp only [Finset.sum_singleton] at hb
  have hrH := mul_nonneg (S.radius_pos hs₀ (E.indices n)).le (H_nonneg q p.2)
  refine ⟨mul_nonneg (S.radius_pos hs₀ _).le (mul_nonneg (H_nonneg q p.2) (hc.2.1 _ _)),?_⟩
  calc
    _ = S.radius (E.indices n)*H q p.2*
        (F.approximation (E.indices n)).cold (E.coldLabel k a n)
          (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2)) := by
      dsimp [coldLabelDensity]
      ring
    _ ≤ S.radius (E.indices n)*H q p.2*(2*(F.approximation (E.indices n)).amplitude) :=
      mul_le_mul_of_nonneg_left hb hrH
    _ = _ := by ring

theorem HotLimitExtraction.coldLabelDensity_fiber_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ)
    (x : JetPrototype.Space) : Integrable (fun v => E.coldLabelDensity k a n t (x,v)) := by
  have hm : Measurable (fun v => E.coldLabelDensity k a n t (x,v)) :=
    (E.coldLabelDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq k a n t).comp
    (measurable_const.prodMk measurable_id)
  apply ((integrable_H hq).const_mul
    (S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude))).mono' hm.aestronglyMeasurable
  filter_upwards [] with v
  have hb := E.coldLabelDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq k a n t (x,v)
  simpa only [Real.norm_of_nonneg hb.1] using hb.2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The limiting average of an individual cold label -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelLimitProfile (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  let μ := E.phase*Real.exp (η*(k:ℝ))
  JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
    ((JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*(1/4))

theorem HotLimitExtraction.coldLabelLimitProfile_measurable (E : HotLimitExtraction S)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 ≤ t)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (E.coldLabelLimitProfile k a t ψ) := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  exact (JetCoreDensity.limitingCoefficient_measurable hα hγ hμ ht K (JetPrototype.sign a) hψ).mul
    (((measurable_const.indicator (JetGeometry.measurableSet_scaleShell η
      (E.phase*Real.exp (η*(k:ℝ))))).comp measurable_fst).mul_const (1/4))

theorem HotLimitExtraction.coldLabelLimitProfile_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : JetPrototype.Space) :
    |E.coldLabelLimitProfile k a t ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hc := JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x
  have hm : |(JetGeometry.scaleShell η (E.phase*Real.exp (η*(k:ℝ)))).indicator
      (fun _ => (1:ℝ)) x.1*(1/4)| ≤ 1 := by
    classical
    by_cases hx : x.1 ∈ JetGeometry.scaleShell η (E.phase*Real.exp (η*(k:ℝ))) <;> norm_num [hx]
  unfold coldLabelLimitProfile
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) hm).trans hc

theorem HotLimitExtraction.coldLabelLimitProfile_integrable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (E.coldLabelLimitProfile k a t ψ) ρ :=
  Integrable.of_bound (E.coldLabelLimitProfile_measurable hα.le hγ.le k a ht.le hψ).aestronglyMeasurable
    _ (ae_of_all _ (fun x => E.coldLabelLimitProfile_bound hK hα hγ k a ht hψB x))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Removing the stripes from an individual cold-label profile -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_striped_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t)
    (Ω : Set JetPrototype.Space) (hΩ : MeasurableSet Ω) (hΩfin : JetPrototype.spaceVolume Ω < ⊤)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges (JetPrototype.spaceVolume.restrict Ω)
      (fun n => E.coldLabelStripedProfile k a n t ψ) (E.coldLabelLimitProfile k a t ψ) := by
  let ρ := JetPrototype.spaceVolume.restrict Ω
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hΩfin.ne
  let μ := E.phase*Real.exp (η*(k:ℝ))
  let c := JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ
  let m : JetPrototype.Space → ℝ := fun x =>
    (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hcm : Measurable c := JetCoreDensity.limitingCoefficient_measurable
    hα.le hγ.le hμ ht.le K (JetPrototype.sign a) hψ
  have hci : Integrable c ρ := Integrable.of_bound hcm.aestronglyMeasurable _
    (ae_of_all _ (fun x => JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB _ x))
  have hmm : Measurable m :=
    (measurable_const.indicator (JetGeometry.measurableSet_scaleShell η μ)).comp measurable_fst
  have hmb (x) : |m x| ≤ 1 := by
    classical
    by_cases hx : x.1 ∈ JetGeometry.scaleShell η μ <;> simp [m,hx]
  have hli := E.coldLabelLimitProfile_integrable hK hα hγ k a ht hψ hψB ρ
  refine ⟨E.coldLabelLimitProfile_measurable hα.le hγ.le k a ht.le hψ,hli,?_⟩
  intro φ hφ hφB
  obtain ⟨D,hD⟩ := hφB
  let χ : JetPrototype.Space → ℝ := fun x => φ x*(m x*c x)
  have hχi : Integrable χ ρ :=
    (hci.bdd_mul hmm.aestronglyMeasurable (ae_of_all _ hmb)).bdd_mul
      hφ.aestronglyMeasurable (ae_of_all _ hD)
  have hzero := ((E.coldLabelStripe_space_centered_weakStar hs₀ hη k a t).restrict hΩ).2 χ hχi
  have hi (n) := (E.coldLabelStripedProfile_integrable hK hα hγ k a n ht hψ hψB ρ).bdd_mul
    hφ.aestronglyMeasurable (ae_of_all _ hD)
  have hl := hli.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hD)
  have heq (n) : (∫ x, χ x*(E.coldLabelStripeAverage k a n t x.1-1/4) ∂ρ) =
      (∫ x, φ x*E.coldLabelStripedProfile k a n t ψ x ∂ρ)-
        (∫ x, φ x*E.coldLabelLimitProfile k a t ψ x ∂ρ) := by
    rw [← integral_sub (hi n) hl]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [χ,m,c,μ,coldLabelStripedProfile,coldLabelLimitProfile]
    ring
  simp only [mul_zero,integral_zero] at hzero
  change Tendsto (fun n => ∫ x, χ x*(E.coldLabelStripeAverage k a n t x.1-1/4) ∂ρ)
    atTop (𝓝 0) at hzero
  simp_rw [heq] at hzero
  simpa only [zero_add,sub_add_cancel] using
    hzero.add_const (∫ x, φ x*E.coldLabelLimitProfile k a t ψ x ∂ρ)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Joint measurability and positive-time bounds of the atomic label limits -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelLimitProfile_clamped_measurable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (k : ℤ) (a : Bool)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun z : ℝ × JetPrototype.Space => E.coldLabelLimitProfile k a (max 0 z.1) ψ z.2) := by
  let μ := E.phase*Real.exp (η*(k:ℝ))
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hmA := (AxialBackground.clamped_atom_test_measurable hK hα hγ hμ (JetPrototype.sign a) hψ).comp
    (measurable_fst.prodMk measurable_snd.snd :
      Measurable (fun z : ℝ × JetPrototype.Space => (z.1,z.2.2)))
  have hmS : Measurable (fun z : ℝ × JetPrototype.Space =>
      (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) z.2.1) :=
    (measurable_const.indicator (JetGeometry.measurableSet_scaleShell η μ)).comp measurable_snd.fst
  have heq : (fun z : ℝ × JetPrototype.Space => E.coldLabelLimitProfile k a (max 0 z.1) ψ z.2) =
      (fun z => (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) z.2.1*
        (∫ v, ψ v ∂AxialBackground.atom K α γ μ (max 0 z.1) (JetPrototype.sign a) z.2.2)) := by
    funext z
    rw [AxialBackground.integral_atom hK hα hγ hμ (le_max_left _ _)]
    unfold coldLabelLimitProfile AxialBackground.weight JetCoreDensity.limitingCoefficient
    dsimp only [μ]
    ring
  rw [heq]
  exact hmS.mul hmA

theorem HotLimitExtraction.coldLabelLimitProfile_slab_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (σ : Bool)
    {a t B : ℝ} (ha : 0 < a) (ht : a ≤ t) {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B)
    (x : JetPrototype.Space) :
    |E.coldLabelLimitProfile k σ t ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/a)*B := by
  have hb := E.coldLabelLimitProfile_bound hK hα hγ k σ (ha.trans_le ht) hψB x
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha ht) hB)

theorem HotLimitExtraction.coldLabelLimitProfile_clamped_integrable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (σ : Bool)
    {a A B : ℝ} (ha : 0 < a) {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (fun z => E.coldLabelLimitProfile k σ (max 0 z.1) ψ z.2)
      ((volume.restrict (Icc a A)).prod ρ) := by
  apply Integrable.of_bound
    (E.coldLabelLimitProfile_clamped_measurable hK hα.le hγ.le k σ hψ).aestronglyMeasurable
    (((K*max 1 (α*γ)⁻¹)/a)*B)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
  rw [Real.norm_eq_abs,max_eq_right (ha.le.trans hz.1)]
  exact E.coldLabelLimitProfile_slab_bound hK hα hγ k σ ha hz.1 hψB z.2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # L1 comparison of the actual and free cold velocity averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_average_free_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => ∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x|
      ∂JetPrototype.spaceVolume.restrict Ω) atTop (𝓝 0) := by
  have hl := E.coldLabel_average_error_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq k a hk ht htU Ω hΩ hψB
  apply hl.congr'
  filter_upwards [S.eventually_scaled_slab hs₀ E.horizon_limit htU] with n hn
  have htime : S.radius (E.indices n)*t ≤ 1 :=
    (hn t ⟨ht.le,le_rfl⟩).2.trans
      (((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le).trans (by norm_num))
  apply integral_congr_ae
  filter_upwards [E.coldLabelAverage_sub_free hs₀ hsmax hη hηmax hK hα hγ hd₀ hq
    k a n ht htime Ω hΩ hψ hψB] with x hx
  rw [hx]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual cold averages converge to the shell-weighted stripe averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_actual_striped_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω₁ : Set Transverse) (hΩ₁ : IsCompact Ω₁) (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => ∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelStripedProfile k a n t ψ x|
      ∂JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)) atTop (𝓝 0) := by
  let Ω := Ω₁ ×ˢ Ω₂
  have hΩ : IsCompact Ω := hΩ₁.prod hΩ₂
  let ρ := JetPrototype.spaceVolume.restrict Ω
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  let _ : IsFiniteMeasure ((volume : Measure ℝ).restrict Ω₂) :=
    isFiniteMeasure_restrict.mpr hΩ₂.measure_lt_top.ne
  have hactual := E.coldLabel_average_free_L1_limit hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le
    hd₀ hd₀max hsmall hq k a hk ht htU Ω hΩ hψ.measurable hψB
  have hfree := E.coldLabel_free_striped_L1_limit hs₀ hη hK hα hγ hd₀ k a ht hψ hψB
    Ω₁ hΩ₁.measure_lt_top (volume.restrict Ω₂)
  rw [Measure.prod_restrict] at hfree
  have hlim := hactual.add hfree
  simp only [zero_add] at hlim
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _ hlim
  intro n
  have hiA := E.coldLabelAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k a n t Ω hΩ
    hψ.measurable hψB
  have hiF := E.coldLabelFreeAverage_integrable hs₀ hK hα hγ hd₀ k a n ht hψ hψB ρ
  have hiS := E.coldLabelStripedProfile_integrable hK hα hγ k a n ht hψ hψB ρ
  have hsum : (∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x|+
      |E.coldLabelFreeAverage k a n t ψ x-E.coldLabelStripedProfile k a n t ψ x| ∂ρ) =
      (∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x| ∂ρ)+
      (∫ x, |E.coldLabelFreeAverage k a n t ψ x-E.coldLabelStripedProfile k a n t ψ x| ∂ρ) :=
    integral_add (hiA.sub hiF).abs (hiF.sub hiS).abs
  rw [← hsum]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
    ((hiA.sub hiF).abs.add (hiF.sub hiS).abs)
  exact ae_of_all _ (fun x => abs_sub_le _ _ _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Simultaneous striped approximation on a finite retained mesh -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.finiteColdAverage (E : HotLimitExtraction S) (L U : ℤ)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∑ a : Bool, ∑ k ∈ Finset.Icc L U, if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
    E.coldLabelAverage k a n t ψ x else 0

def HotLimitExtraction.finiteStripedProfile (E : HotLimitExtraction S) (L U : ℤ)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∑ a : Bool, ∑ k ∈ Finset.Icc L U, if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
    E.coldLabelStripedProfile k a n t ψ x else 0

theorem HotLimitExtraction.finite_actual_striped_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (L U : ℤ) {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω₁ : Set Transverse) (hΩ₁ : IsCompact Ω₁) (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => ∫ x, |E.finiteColdAverage L U n t ψ x-E.finiteStripedProfile L U n t ψ x|
      ∂JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)) atTop (𝓝 0) := by
  classical
  let ρ := JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  let f : Bool → ℤ → ℕ → JetPrototype.Space → ℝ := fun a k n x =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
      E.coldLabelAverage k a n t ψ x-E.coldLabelStripedProfile k a n t ψ x else 0
  have hi (a k n) : Integrable (f a k n) ρ := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · exact ((E.coldLabelAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k a n t
        (Ω₁ ×ˢ Ω₂) (hΩ₁.prod hΩ₂) hψ.measurable hψB).sub
          (E.coldLabelStripedProfile_integrable hK hα hγ k a n ht hψ hψB ρ)).congr
            (ae_of_all _ (fun _ => by simp only [f,hk,ite_true]; rfl))
    · simpa only [f,hk,ite_false] using (integrable_const (μ := ρ) (0:ℝ))
  have hl (a k) : Tendsto (fun n => ∫ x, |f a k n x| ∂ρ) atTop (𝓝 0) := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,hk,ite_true] using E.coldLabel_actual_striped_L1_limit hs₀ hsmax hη hηmax
        hK hα hαmax hγ hd₀ hd₀max hsmall hq k a hk ht htU Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
    · simp only [f,hk,ite_false,abs_zero,integral_zero]
      exact tendsto_const_nhds
  have hinner (a) := Compactness.finite_integral_L1_zero (Finset.Icc L U)
    (fun k _ n => hi a k n) (fun k _ => hl a k)
  have houter := Compactness.finite_integral_L1_zero (Finset.univ : Finset Bool)
    (fun a _ n => integrable_finsetSum (Finset.Icc L U) (fun k _ => hi a k n))
    (fun a _ => hinner a)
  convert houter using 1
  funext n
  congr 1
  funext x
  congr 1
  rw [finiteColdAverage,finiteStripedProfile,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)) <;> simp only [f,hk,ite_true,ite_false,sub_self]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The weak limit of an actual retained cold label -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
      (fun n => E.coldLabelAverage k a n t ψ) (E.coldLabelLimitProfile k a t ψ) := by
  let ρ := JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  have hw := E.coldLabel_striped_weak_limit hs₀ hη hK hα hγ k a ht
    (Ω₁ ×ˢ Ω₂) (hΩ₁.prod hΩ₂).measurableSet (hΩ₁.prod hΩ₂).measure_lt_top hψ hψB
  exact hw.of_integral_abs_sub
    (fun n => E.coldLabelStripedProfile_integrable hK hα hγ k a n ht hψ hψB ρ)
    (fun n => E.coldLabelAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k a n t
      (Ω₁ ×ˢ Ω₂) (hΩ₁.prod hΩ₂) hψ.measurable hψB)
    (E.coldLabel_actual_striped_L1_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq k a hk ht htU Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The weak limit of the finite retained cold mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.finiteColdLimitProfile (E : HotLimitExtraction S) (L U : ℤ)
    (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∑ a : Bool, ∑ k ∈ Finset.Icc L U, if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
    E.coldLabelLimitProfile k a t ψ x else 0

theorem HotLimitExtraction.finite_cold_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (L U : ℤ) {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
      (fun n => E.finiteColdAverage L U n t ψ) (E.finiteColdLimitProfile L U t ψ) := by
  classical
  let ρ := JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  let f : Bool → ℤ → ℕ → JetPrototype.Space → ℝ := fun a k n x =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then E.coldLabelAverage k a n t ψ x else 0
  let g : Bool → ℤ → JetPrototype.Space → ℝ := fun a k x =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then E.coldLabelLimitProfile k a t ψ x else 0
  have hi (a k n) : Integrable (f a k n) ρ := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,hk,ite_true] using E.coldLabelAverage_integrable hs₀ hsmax hη hηmax
        hK hd₀.le hq k a n t (Ω₁ ×ˢ Ω₂) (hΩ₁.prod hΩ₂) hψ.measurable hψB
    · simpa only [f,hk,ite_false] using (integrable_const (μ := ρ) (0:ℝ))
  have hw (a k) : Published.WeakL1Converges ρ (f a k) (g a k) := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,g,hk,ite_true] using E.coldLabel_weak_limit hs₀ hsmax hη hηmax
        hK hα hαmax hγ hd₀ hd₀max hsmall hq k a hk ht htU Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
    · simp only [f,g,hk,ite_false]
      refine ⟨measurable_const,integrable_const 0,?_⟩
      intro φ _ _
      simp only [mul_zero,integral_zero]
      exact tendsto_const_nhds
  have hinner (a) := Published.WeakL1Converges.finset_sum (Finset.Icc L U)
    (fun k _ => hw a k) (fun k _ n => hi a k n)
  have houter := Published.WeakL1Converges.finset_sum (Finset.univ : Finset Bool)
    (fun a _ => hinner a)
    (fun a _ n => integrable_finsetSum (Finset.Icc L U) (fun k _ => hi a k n))
  exact houter

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Identifying the finite cold limit with the actual atomic background -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.finiteColdLimitProfile_eq_background (E : HotLimitExtraction S)
    (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    {t δ R : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (x : JetPrototype.Space)
    (hlo : δ ≤ ‖x.1‖) (hhi : ‖x.1‖ ≤ R) (ψ : Velocity → ℝ) :
    E.finiteColdLimitProfile (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η)
      t ψ x = ∫ v, ψ v ∂E.background t x := by
  convert! (GeometricBackground.integral_finite_window E.phase_mem.1 E.phase_mem.2 hη hδ
    hK hα hγ ht x hlo hhi ψ).symm using 1

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The finite cold mesh converges to the geometric background away from the axis -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.background_average_measurable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) {t : ℝ} (ht : 0 ≤ t)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x => ∫ v, ψ v ∂E.background t x) := by
  have hm := (GeometricBackground.clamped_background_test_measurable
    (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ η E.fraction hψ).comp
      (measurable_const.prodMk measurable_id : Measurable (fun x : JetPrototype.Space => (t,x)))
  dsimp only [Function.comp_def] at hm
  simpa only [max_eq_right ht,background] using hm

theorem HotLimitExtraction.finite_cold_background_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {t δ R : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon) (hδ : 0 < δ)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
      (fun n => E.finiteColdAverage (GeometricMesh.index (δ/Real.exp η) η)
        (GeometricMesh.index R η) n t ψ) (fun x => ∫ v, ψ v ∂E.background t x) := by
  have hw := E.finite_cold_weak_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq
    (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) ht htU Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
  apply hw.congr_limit (E.background_average_measurable hK hα.le hγ.le ht.le hψ.measurable)
  filter_upwards [ae_restrict_mem (hΩ₁.prod hΩ₂).measurableSet] with x hx
  exact E.finiteColdLimitProfile_eq_background hη hK hα.le hγ.le ht.le hδ x
    (hlo x.1 hx.1) (hhi x.1 hx.1) ψ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
