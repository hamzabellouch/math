import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMomentBound
import OAI.MathematicalPhysics.Boltzmann.Branching.CommonMomentEnvelope
import OAI.MathematicalPhysics.Boltzmann.Branching.DensityCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSliceIntegration
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularCollisionIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFiniteCap
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTailRegions

namespace OAI

section

/-! # A common velocity moment for the actual capped torus densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

def momentBase (s₀ η K α d₀ q : ℝ) : ℝ :=
  (2+escapedConstant s₀ η K α d₀)*hotConstant q

theorem momentBase_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α q : ℝ) : 0 ≤ momentBase s₀ η K α d₀ q :=
  mul_nonneg (add_nonneg (by norm_num) (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _))
    (hotConstant_nonneg q)

theorem capped_torus_moment {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : WeightedLocalControl.PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    ∀ᵐ x : Position,
      moment (fun v => H q v*F.value
        (t,(JetPeriodicDatum.spatialMap (TorusChart.representative x),v))) ≤
      ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
        (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
          (AnnularEnvelope.torusChart (t,x))) := by
  have hm := capped_cell_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
    hq hb hL hT hR hTmax hδ hδmax hloss N hh₀m hh₀ hF₀ F hcap ht
  have hp := TorusChart.representative_measurePreserving.quasiMeasurePreserving.ae
    (hm.filter_mono MeasureTheory.ae_restrict_le)
  filter_upwards [hp] with x hx
  apply (hx (TorusChart.representative_mem x)).trans (ENNReal.ofReal_le_ofReal ?_)
  exact AnnularEnvelope.affine_le_commonMoment hs₀ hη.le ht.1.le
    (JetEnvelopeGain.momentConstant_nonneg hK α γ) _ _ _

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Spacetime velocity moments of the actual capped periodic solutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

def torusPhysical (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : (ℝ × Position) × Velocity) : ℝ :=
  H q z.2*F (z.1.1,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1.2),z.2))

theorem torusPhysical_measurable {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (q : ℝ) :
    Measurable (torusPhysical q F) := by
  have hrep : Measurable (fun z : (ℝ × Position) × Velocity => TorusChart.representative z.1.2) :=
    TorusChart.representative_measurePreserving.measurable.comp measurable_fst.snd
  have hspace := JetPeriodicDatum.spatialMap_measurePreserving.measurable.comp hrep
  have harg : Measurable (fun z : (ℝ × Position) × Velocity =>
      (z.1.1,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1.2),z.2))) :=
    measurable_fst.fst.prodMk (hspace.prodMk measurable_snd)
  have hw : Measurable (fun z : (ℝ × Position) × Velocity => H q z.2) := by
    unfold H singularity
    fun_prop
  exact hw.mul (hFm.comp harg)

theorem torusPhysical_nonneg {F : ℝ × JetPrototype.Phase → ℝ} (hF : ∀ u, 0 ≤ F u)
    (q : ℝ) (z : (ℝ × Position) × Velocity) : 0 ≤ torusPhysical q F z :=
  mul_nonneg (H_nonneg q z.2) (hF _)

theorem capped_spacetime_moment {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : WeightedLocalControl.PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
 :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T,
      moment (fun v => torusPhysical q F.value (u,v)) ≤
      ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
        (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
          (AnnularEnvelope.torusChart u)) := by
  apply Compactness.ae_interval_of_slices
  · exact measurableSet_le (measurable_moment (torusPhysical_measurable F.measurable_value q))
      (ENNReal.measurable_ofReal.comp ((AnnularEnvelope.commonMoment_measurable s₀ η _ _).comp
        AnnularEnvelope.torusChart_measurable))
  · intro t ht
    exact capped_torus_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
      hq hb hL hT hR hTmax hδ hδmax hloss N hh₀m hh₀ hF₀ F hcap ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Fixed outer-annulus velocity majorants for the actual capped torus densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_torus_outer_bound {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N J : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : WeightedLocalControl.PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    ∀ᵐ x : Position, ∀ᵐ v : Velocity,
      (t,x) ∉ AnnularEnvelope.torusTail s₀ η J → torusPhysical q F.value ((t,x),v) ≤
        (2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J)*H q v := by
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ R := ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hm : Measurable (initial s₀ η K α γ d₀ q N h₀) :=
    (measurable_seed s₀ η K α γ d₀ q N).add hh₀m
  have hz := F.hot_size_le_cap hq hb hL hT hR hδ hloss hm hF₀
    (measurable_color s₀ η K α γ d₀ q N) hc₀ hi.2 hcap t ⟨ht.1.le,ht.2⟩
  have hz2 : PhaseEssSup.size (fun p => F.value (t,p)-∑' i,
      rebuilt s₀ η K α γ d₀ q b L T N F.value i (t,p)) ≤ 2 := by
    exact hz.trans (by linarith [ht.2])
  have ho := rebuilt_cell_outer_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
    hq hb hL hT hR hTmax hloss N J hh₀ F.measurable_value F.value_bounds hF₀
    (F.all_mild hT) ht hz2
  have hp := TorusChart.representative_measurePreserving.quasiMeasurePreserving.ae
    (ho.filter_mono MeasureTheory.ae_restrict_le)
  filter_upwards [hp] with x hx
  by_cases hxt : (t,x) ∈ AnnularEnvelope.torusTail s₀ η J
  · exact ae_of_all _ (fun _ hn => False.elim (hn hxt))
  · have houter (j : ℕ) (hj : J ≤ j) :
        transverse (TorusChart.representative x) ∉ AnnularEnvelope.shell s₀ η j := by
      intro hmem
      exact hxt ⟨j,hj,hmem⟩
    have hr := hx (TorusChart.representative_mem x) houter
    filter_upwards [hr] with v hv
    intro _
    exact (mul_le_mul_of_nonneg_left hv (H_nonneg q v)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Spacetime outer-annulus majorants for actual capped periodic solutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_spacetime_outer_bound {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N J : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : WeightedLocalControl.PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
 :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T, ∀ᵐ v : Velocity,
      u ∉ AnnularEnvelope.torusTail s₀ η J → torusPhysical q F.value (u,v) ≤
        (2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J)*H q v := by
  apply Compactness.ae_interval_nested_of_slices (T := T)
    (ν := (volume : Measure Position)) (ρ := (volume : Measure Velocity))
    (P := fun z : (ℝ × Position) × Velocity =>
      z.1 ∉ AnnularEnvelope.torusTail s₀ η J → torusPhysical q F.value z ≤
        (2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J)*H q z.2)
  · have hs := (AnnularEnvelope.torusTail_measurable s₀ η J).preimage
      (measurable_fst : Measurable (Prod.fst : (ℝ × Position) × Velocity → ℝ × Position))
    have hm : Measurable (fun z : (ℝ × Position) × Velocity =>
        (2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J)*H q z.2) := by
      unfold H singularity
      fun_prop
    convert hs.union (measurableSet_le (torusPhysical_measurable F.measurable_value q) hm) using 1
    ext z
    simp only [mem_union,mem_preimage,mem_ofPred_eq,imp_iff_not_or,not_not]
  · intro t ht
    exact capped_torus_outer_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
      hq hb hL hT hR hTmax hδ hδmax hloss N J hh₀m hh₀ hF₀ F hcap ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform collision-pair integrability for the actual capped approximation family -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_family_pairs_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (b L R δ : ℕ → ℝ) (h₀ : ℕ → JetPrototype.Phase → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
    (hδ : ∀ n, 0 < δ n) (hδmax : ∀ n, δ n ≤ 1)
    (hloss : ∀ n, R n*CutoffLipschitz.frequencyConstant q (b n) ≤ L n)
    (hh₀m : ∀ n, Measurable (h₀ n)) (hh₀ : ∀ n p, 0 ≤ h₀ n p)
    (hF₀ : ∀ n p, initial s₀ η K α γ d₀ q n (h₀ n) p ≤ R n)
    (F : ∀ n, PeriodicMildState q (b n) (L n) T (R n) (initial s₀ η K α γ d₀ q n (h₀ n)))
    (hcap : ∀ n, (F n).hotPeak (δ n) (color s₀ η K α γ d₀ q n) ≤ 1) :
    UniformIntegrable (fun n => CollisionCompactness.pairDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) := by
  apply CollisionCompactness.annular_pairs_uniformIntegrable hs₀ hη hηmax hT hq
    (momentBase_nonneg hs₀ hK hd₀ η α q) (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    (fun n => torusPhysical_measurable (F n).measurable_value q)
    (fun n => torusPhysical_nonneg (fun u => ((F n).value_bounds u).1) q)
  · intro n
    exact capped_spacetime_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
      hq (hb n) (hL n) hT (hR n) hTmax (hδ n) (hδmax n) (hloss n) n
      (hh₀m n) (hh₀ n) (hF₀ n) (F n) (hcap n)
  · intro J
    refine ⟨2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J,?_,?_⟩
    · exact add_nonneg (add_nonneg (by norm_num)
        (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _))
        (finiteAmplitude_nonneg hs₀ hK hd₀ η α J)
    · intro n
      exact capped_spacetime_outer_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
        hq (hb n) (hL n) hT (hR n) hTmax (hδ n) (hδmax n) (hloss n) n J
        (hh₀m n) (hh₀ n) (hF₀ n) (F n) (hcap n)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The constructed approximation sequence with uniformly integrable collision pairs -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

structure CapApproximation (s₀ η K α γ d₀ q T : ℝ) (N : ℕ) where
  amplitude : ℝ
  coefficient : ℝ
  amplitude_pos : 0 < amplitude
  coefficient_mem : coefficient ∈ Icc 0 2
  initial_bound : ∀ p, initial s₀ η K α γ d₀ q N
    (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*amplitude
  solution : PeriodicMildState q (N+1) (damping q (N+1) amplitude) T (2*amplitude)
    (initial s₀ η K α γ d₀ q N
      (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p))
  cap : solution.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) = 1

theorem cap_family_pairs_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, CapApproximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun N => CollisionCompactness.pairDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) := by
  have hδ (n) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hhn (n) (p) : 0 ≤ (F n).coefficient*
      HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds (hδ n) (hδmax n) q
    exact mul_nonneg (F n).coefficient_mem.1 (hb p).1
  exact capped_family_pairs_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap.le)

theorem exists_integrable_cap_family (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1/32 ∧ ∃ F : ∀ N, CapApproximation s₀ η K α γ d₀ q T N,
      UniformIntegrable (fun N => CollisionCompactness.pairDensity (torusPhysical q (F N).solution.value)) 1
        ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
      Tendsto (fun N => ∫ p, ‖periodicInitial s₀ η K α γ d₀ q N (F N).coefficient p-
        JetPeriodicDatum.datum s₀ η K α γ d₀ p‖) atTop (𝓝 0) := by
  obtain ⟨T,hT,hTmax,hcap⟩ := exists_uniform_cap_solution hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  have hn (N : ℕ) : Nonempty (CapApproximation s₀ η K α γ d₀ q T N) := by
    obtain ⟨A,ell,hA,hell,hinit,F,hF⟩ := hcap N (N+1) T (by positivity) hT.le le_rfl
    exact ⟨⟨A,ell,hA,hell,hinit,F,hF⟩⟩
  let F := fun N => Classical.choice (hn N)
  refine ⟨T,hT,hTmax,F,?_,?_⟩
  · exact cap_family_pairs_uniformIntegrable hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ hT.le hTmax F
  · exact periodicInitial_L1_tendsto hs₀ hsmax hη hηmax hK hγ hd₀
      (by linarith) hq₂ α (fun N => (F N).coefficient_mem)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform integrability of the actual capped one-particle densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_family_density_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (b L R δ : ℕ → ℝ) (h₀ : ℕ → JetPrototype.Phase → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
    (hδ : ∀ n, 0 < δ n) (hδmax : ∀ n, δ n ≤ 1)
    (hloss : ∀ n, R n*CutoffLipschitz.frequencyConstant q (b n) ≤ L n)
    (hh₀m : ∀ n, Measurable (h₀ n)) (hh₀ : ∀ n p, 0 ≤ h₀ n p)
    (hF₀ : ∀ n p, initial s₀ η K α γ d₀ q n (h₀ n) p ≤ R n)
    (F : ∀ n, PeriodicMildState q (b n) (L n) T (R n) (initial s₀ η K α γ d₀ q n (h₀ n)))
    (hcap : ∀ n, (F n).hotPeak (δ n) (color s₀ η K α γ d₀ q n) ≤ 1) :
    UniformIntegrable (fun n => torusPhysical q (F n).value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  apply CollisionCompactness.annular_density_uniformIntegrable hs₀ hη hηmax hT hq
    (momentBase_nonneg hs₀ hK hd₀ η α q) (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    (fun n => torusPhysical_measurable (F n).measurable_value q)
    (fun n => torusPhysical_nonneg (fun u => ((F n).value_bounds u).1) q)
  · intro n
    exact capped_spacetime_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
      hq (hb n) (hL n) hT (hR n) hTmax (hδ n) (hδmax n) (hloss n) n
      (hh₀m n) (hh₀ n) (hF₀ n) (F n) (hcap n)
  · intro J
    refine ⟨2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J,?_,?_⟩
    · exact add_nonneg (add_nonneg (by norm_num)
        (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _))
        (finiteAmplitude_nonneg hs₀ hK hd₀ η α J)
    · intro n
      exact capped_spacetime_outer_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
        hq (hb n) (hL n) hT (hR n) hTmax (hδ n) (hδmax n) (hloss n) n J
        (hh₀m n) (hh₀ n) (hF₀ n) (F n) (hcap n)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # One-particle uniform integrability for the constructed cap sequence -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_family_density_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, CapApproximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun N => torusPhysical q (F N).solution.value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hδ (n) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hhn (n) (p) : 0 ≤ (F n).coefficient*
      HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds (hδ n) (hδmax n) q
    exact mul_nonneg (F n).coefficient_mem.1 (hb p).1
  exact capped_family_density_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap.le)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
