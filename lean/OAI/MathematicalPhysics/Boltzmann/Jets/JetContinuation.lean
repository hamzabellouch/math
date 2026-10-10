import OAI.MathematicalPhysics.Boltzmann.Approximation.MildInitialAE
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCoordinates
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdTime
import OAI.MathematicalPhysics.Boltzmann.Branching.FamilyHotBounds
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPhysicalSource
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotCapBound
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedCharacteristic
import OAI.MathematicalPhysics.Boltzmann.Branching.ZeroProfileParameters
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricColdSource
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds

namespace OAI

section

/-! # Total norm control for a reconstructed geometric decomposition -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_total_norm_le {s₀ η K α γ d₀ q b L T R Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) (t,p)))
    (hper : ∀ n, pull (displacement n) F = F) {t : ℝ} (ht : t ∈ Ioc 0 T)
    (hz : PhaseEssSup.size (fun p => F (t,p)-∑' i, rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ Z) :
    PhaseEssSup.size (fun p => F (t,p)) ≤ coldNormBound s₀ η K α d₀ N+Z := by
  let c := rebuilt s₀ η K α γ d₀ q b L T N F
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hcb (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧ color s₀ η K α γ d₀ q N i p ≤ R :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hcb hi.2 hFeq
  have hcn (i) (u) : 0 ≤ c i u := (hp.2.1 i u).1
  have hbound : ∀ p : JetPrototype.Phase, (∑' i, c i (t,p)) ≤ coldNormBound s₀ η K α d₀ N :=
    geometric_cold_sum_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hTmax hsmall N
      hcn (fun u => (hp.2.2.2.1 u).1)
      (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun u => (hF u).1))
      (fun r hr i x w => rebuilt_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hb hL hT hR
        (hTmax.trans (by norm_num)) hloss N hh₀ hFm hF hF₀ i hr (JetPeriodicDatum.spatialMap x,w))
      (fun n i => rebuilt_shift n (hper n) i) t ht
  exact PhaseEssSup.size_le_cold_add_hot
    (hFm.comp (measurable_const.prodMk measurable_id))
    ((Measurable.tsum hp.1).comp (measurable_const.prodMk measurable_id))
    (coldNormBound_nonneg hs₀ hK hd₀ η α N) (fun p => hF (t,p))
    (fun p => ⟨tsum_nonneg (fun i => hcn i (t,p)),(hp.2.2.2.1 (t,p)).2⟩) hbound hz

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Velocity moment envelope for the actual rebuilt positive solutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.JetGeometry BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_cell_moment {s₀ η K α γ d₀ q b L T R Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hZ : 0 ≤ Z)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) (t,p)))
    {t : ℝ} (ht : t ∈ Ioc 0 T)
    (hsize : PhaseEssSup.size (fun p => F (t,p)-∑' i,
      rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ Z) :
    ∀ᵐ x : Velocity, x ∈ TorusChart.cube →
      moment (fun v => H q v*F (t,(JetPeriodicDatum.spatialMap x,v))) ≤ ENNReal.ofReal
        ((Z+escapedConstant s₀ η K α d₀)*hotConstant q+
          JetEnvelopeGain.momentConstant K α γ*
            AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x)) := by
  let c := rebuilt s₀ η K α γ d₀ q b L T N F
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ R := ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hc₀ hi.2 hFeq
  have hcn (i) (u) : 0 ≤ c i u := (hp.2.1 i u).1
  have hh := family_hot_bounds hq hb hR hloss hFm hp.1 hF hcn hp.2.2.1
  have hae := PhaseEssSup.ae_abs_le_size
    (hh.1.comp (measurable_const.prodMk measurable_id))
    (fun p => show |F (t,p)-∑' i, c i (t,p)| ≤ R from by
      change |F (t,p)-∑' i, rebuiltColdFamily q b L T F (color s₀ η K α γ d₀ q N) i (t,p)| ≤ R
      rw [abs_of_nonneg (hh.2.1 (t,p)).1]
      exact (hh.2.1 (t,p)).2)
  have hz : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (t,p)-∑' i, c i (t,p) ≤ Z := by
    filter_upwards [hae] with p hp'
    exact (le_abs_self _).trans (hp'.trans hsize)
  have hm := JetPeriodicDatum.phaseMap_measurePreserving.quasiMeasurePreserving.ae hz
  rw [Measure.volume_eq_prod] at hm
  have hs := Measure.ae_ae_of_ae_prod hm
  filter_upwards [hs] with x hxhot
  intro hx
  apply cell_moment_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hq hZ
    ht.1 (ht.2.trans hTmax) hsmall N x hx
    (fun v => F (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i v => c i (t,(JetPeriodicDatum.spatialMap x,v)))
  · intro i
    exact (hp.1 i).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  · exact fun i v => hcn i _
  · exact fun v => (hp.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))).1
  · intro i hi v
    exact congrFun (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun u => (hF u).1) i hi) _
  · intro i v
    exact rebuilt_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall hq hb hL hT hR
      (hTmax.trans (by norm_num)) hloss N hh₀ hFm hF hF₀ i ht (JetPeriodicDatum.spatialMap x,v)
  · exact hxhot

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The whole reconstructed cold family is bounded also at the initial time -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_cold_sum_ae {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) (t,p)))
    (hper : ∀ n, pull (displacement n) F = F) :
    ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (∑' i, rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤
        WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N := by
  let c := rebuilt s₀ η K α γ d₀ q b L T N F
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧ color s₀ η K α γ d₀ q N i p ≤ R :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hc₀ hi.2 hFeq
  have hcn (i) (u) : 0 ≤ c i u := (hp.2.1 i u).1
  have hamp : 0 ≤ WeightedFiniteSeed.amplitude s₀ η K d₀ N :=
    (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N).le
  have hcold : 0 ≤ coldNormBound s₀ η K α d₀ N := coldNormBound_nonneg hs₀ hK hd₀ η α N
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hae : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ i,
        c i (0,p) = color s₀ η K α γ d₀ q N i p :=
      ae_all_iff.mpr (fun i => (hp.2.2.2.2 i).initial_ae hT)
    filter_upwards [hae] with p hcp
    change (∑' i, c i (0,p)) ≤ _
    simp only [hcp]
    exact (seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα hαmax γ q N p).2.trans
      (le_add_of_nonneg_right hcold)
  · have htpos : t ∈ Ioc 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
    have hbound : ∀ p : JetPrototype.Phase, (∑' i, c i (t,p)) ≤ coldNormBound s₀ η K α d₀ N :=
      geometric_cold_sum_bound hs₀ hsmax hη hηmax hK hα (hαmax.trans (by norm_num)) hγ hd₀ hd₀max
        hTmax hsmall N hcn (fun u => (hp.2.2.2.1 u).1)
        (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun u => (hF u).1))
        (fun r hr i x w => rebuilt_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hb hL hT hR
          (hTmax.trans (by norm_num)) hloss N hh₀ hFm hF hF₀ i hr (JetPeriodicDatum.spatialMap x,w))
        (fun n i => rebuilt_shift n (hper n) i) t htpos
    exact ae_of_all _ (fun p => (hbound p).trans (le_add_of_nonneg_left hamp))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The complete core loss estimate from the hot cap and proved escaped tails -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def escapedFrequencyConstant (s₀ η α K d₀ q : ℝ) (m : ℕ) : ℝ :=
  JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m:ℝ))*
    weightFrequencyConstant q 2

theorem escapedFrequencyConstant_nonneg {s₀ K d₀ : ℝ}
    (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀) (η α q : ℝ) (m : ℕ) :
    0 ≤ escapedFrequencyConstant s₀ η α K d₀ q m :=
  mul_nonneg (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)
    (weightFrequencyConstant_nonneg q (by norm_num))

theorem frequency_at_main_cap {s₀ η K α γ d₀ q t δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hq : q < 2) (hδ : 0 ≤ δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (m N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (i : Label) (hi : x ∈ spatialEnlargement s₀ η t i)
    {F : Velocity → ℝ} (hFm : Measurable F) (hFn : ∀ w, 0 ≤ F w)
    (c : Label → Velocity → ℝ) (hcn : ∀ j w, 0 ≤ c j w)
    (hcs : ∀ w, Summable (fun j => c j w))
    (hzero : ∀ j, ¬j.annulus < N → ∀ w, c j w = 0)
    (hhot : ∀ᵐ w, F w-(∑' j, c j w) ≤ t+δ)
    (hcU : ∀ j w, H q w*c j w ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j.annulus) (d₀*jetScale s₀ η j.annulus^10) t j.positive
      (JetSpatialBox.shifted x j.lattice,w)) (b : ℝ) {v : Velocity}
    (hv : ‖v-JetBarrier.centerVelocity α γ (jetScale s₀ η i.annulus) t i.positive
      (JetSpatialBox.shifted x i.lattice)‖ ≤ d₀*jetScale s₀ η i.annulus^10)
    (hv2 : ‖v‖ ≤ 2) :
    CollisionCutoff.frequency b (fun w => H q w*F w) v ≤
      4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9+
        weightFrequencyConstant q 2*(t+δ)+escapedFrequencyConstant s₀ η α K d₀ q m*t^m := by
  let C := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m:ℝ))
  have hC : 0 ≤ C := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have htail (w : Velocity) : (∑' j, escaped s₀ η t N x (fun k => c k w) j) ≤ C*t^m := by
    simpa only [Real.rpow_natCast] using normalized_escaped_bound hs₀ hsmax hη hηmax
      hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall (m:ℝ) q N
      (fun j => c j w) x w hx (fun j => hcn j w) (hcs w) (fun j _ => hcU j w)
  have h := frequency_at_main hs₀ hsmax hη hηmax hK hα hγ hd₀ ht htmax hq
    (add_nonneg ht.le hδ) (mul_nonneg hC (pow_nonneg ht.le m)) hsmall N x i hi
    hFm hFn c hcs hzero hhot htail (hcU i) b hv hv2
  convert h using 1
  unfold escapedFrequencyConstant C
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The geometric cold estimate supplies the total bound used in cap selection -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_total_bound {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1) :
    ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (t,p) ≤
      WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N+T+δ := by
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧ color s₀ η K α γ d₀ q N i p ≤ R :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  apply PeriodicMildState.total_bound_of_cap hq hb hL hT hR hδ hloss
    ((measurable_seed s₀ η K α γ d₀ q N).add hh₀m) hF₀
    (measurable_color s₀ η K α γ d₀ q N) hc₀ hi.2 F hcap
  exact rebuilt_cold_sum_ae hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hwidth hsmall
    hq hb hL hT hR hTmax hloss N hh₀ F.measurable_value F.value_bounds hF₀ (F.all_mild hT) F.periodic

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Total weighted norm control from the cold family and hot norm -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem total_norm_le {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) u)
    (hperiodic : ∀ n, pull (displacement n) F = F)
    {t Z : ℝ} (ht : t ∈ Ioc 0 T)
    (hz : PhaseEssSup.size (fun p => hotRemainder q b L T F (color s₀ η K α γ d₀ q N) (t,p)) ≤ Z) :
    PhaseEssSup.size (fun p => F (t,p)) ≤ coldNormBound s₀ η K α d₀ N+Z := by
  let c := cold s₀ η K α γ d₀ q b L T N F
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc (i : JetLattice.Label) := coldLimit_solution hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N i) hF (hi.1 i) hF₀ hFeq
  have hcm (i) : Measurable (c i) := (hc i).1
  have hcn (i) (p : JetPrototype.Phase) : 0 ≤ c i (t,p) := ((hc i).2.1 (t,p)).1
  have hcs (p : JetPrototype.Phase) := WeightedLocal.cold_family_summable hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hi.1 hF₀ hi.2 hFeq (t,p)
  apply PhaseEssSup.size_le_cold_add_hot
    (hFm.comp (measurable_const.prodMk measurable_id))
    ((Measurable.tsum hcm).comp (measurable_const.prodMk measurable_id))
    (coldNormBound_nonneg hs₀ hK hd₀ η α N) (fun p => hF (t,p))
    (fun p => ⟨tsum_nonneg (fun i => hcn i p),(hcs p).2⟩)
    (cold_sum_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
      hq hb hL hT hR hTmax hloss N hh₀ hFm hF hF₀ hFeq hperiodic t ht)
  exact hz

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Integrability of the spatial thermal-reduction error -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_error_integrable {r K α γ s d μ t B : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hd : 0 < d) (hμ : 0 < μ) (ht : 0 < t)
    (η : ℝ) (a : Bool) {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (fun x => (∫ v, r*JetFreeTransport.free η K α γ s d (r*t) a (r • x,v)*ψ v)-
      limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, dilatedMask r η (s/r) d t a x w*JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)) ρ := by
  have hm := (free_average_measurable r η K α γ s d t a hψ.measurable).sub
    ((limitingCoefficient_measurable hα.le hγ.le hμ ht.le K (JetPrototype.sign a) hψ).mul
      (mask_average_measurable r η (s/r) d t a))
  apply Integrable.of_bound hm.aestronglyMeasurable (2*(((K*max 1 (α*γ)⁻¹)/t)*B))
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  dsimp only [Pi.sub_apply,Pi.mul_apply]
  apply (abs_sub _ _).trans
  have hf := dilated_free_average_bound hr hK hα hγ hs hd ht η a x hψ hψB
  have hc := limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x
  have hb := masked_thermal_bound (dilatedMask_abs_le r η (s/r) d t a x)
  have hp : |limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
      (∫ w, dilatedMask r η (s/r) d t a x w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hb).trans hc
  linarith

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Quantitative survival of central cold colors under the actual cap bounds -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem survival_of_capped_family {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ j, Measurable (c j))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ j z, 0 ≤ c j z ∧ c j z ≤ R)
    (hmild : ColdMildAE q b L T F (color s₀ η K α γ d₀ q N i) (c i))
    (hsum : ∀ z, Summable (fun j => c j z))
    (hzero : ∀ j, ¬j.annulus < N → c j = 0)
    (hU : ∀ r ∈ Ioc 0 T, ∀ j p, H q p.2*c j (r,p) ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j.annulus) (d₀*jetScale s₀ η j.annulus^10) r j.positive
        (shift (displacement j.lattice) p))
    (hcap : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      F (r,p)-(∑' j, c j (r,p)) ≤ r+δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-coldOpticalDepth
        (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
        (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t)*
        color s₀ η K α γ d₀ q N i p ≤ c i (t,JetBarrier.flight t p) := by
  let B := 4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9
  let A := weightFrequencyConstant q 2
  let D := escapedFrequencyConstant s₀ η α K d₀ q m
  have hhotm : Measurable (fun z => F z-∑' j, c j z) := hFm.sub (Measurable.tsum hcm)
  have hpath := ae_velocity_bound_along_paths (T := t) hhotm
    (show Measurable (fun r : ℝ => r+δ) by fun_prop)
    (fun r hr => hcap r ⟨hr.1,hr.2.trans ht.2⟩)
  have hν : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      color s₀ η K α γ d₀ q N i p ≠ 0 →
      ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) t),
        CollisionCutoff.frequency b (fun v => physical q F
          (r,((JetBarrier.flight r p).1,v))) p.2 ≤ B+A*(r+δ)+D*r^m := by
    filter_upwards [hpath] with p hp hp0
    filter_upwards [hp,ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with r hr hrmem hrne
    have hrpos : 0 < r := lt_of_le_of_ne hrmem.1 hrne.symm
    have hrT : r ≤ T := hrmem.2.trans ht.2
    have hgeom := color_flight_geometry hs₀ hα hαmax hγ hd₀ hrpos.le i p hdmax
      ((mul_le_mul_of_nonneg_right hrT (by positivity)).trans hwidth) hp0
    let x : Velocity := PlaneChart.join (JetBarrier.flight r p).1.1 (JetBarrier.flight r p).1.2
    have hx := central_enlargement_coordinates hs₀ hsmax hη
      (hrT.trans hTmax) hi0 hgeom.1
    have hrate := frequency_at_main_cap hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hrpos (hrT.trans hTmax) hq hδ
      hsmall m N x hx i hgeom.1
      (hFm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      (fun w => (hF (r,((JetBarrier.flight r p).1,w))).1)
      (fun j w => c j (r,((JetBarrier.flight r p).1,w)))
      (fun j w => (hc j _).1) (fun w => hsum _)
      (fun j hj w => congrFun (hzero j hj) _)
      hr (fun j w => ?_) b hgeom.2.1 hgeom.2.2
    · exact hrate
    · simpa only [x,JetSpatialBox.shifted,PlaneChart.transverse_join,PlaneChart.axial_join,
        shift,displacement,Prod.sub_def] using hU r ⟨hrpos,hrT⟩ j ((JetBarrier.flight r p).1,w)
  have h := ColdMildAE.survival hq hb hR hloss hFm (hcm i)
    (measurable_color s₀ η K α γ d₀ q N i) hF (hc i) hmild ht
    (fun _ => coldOpticalDepth B A δ D m) (fun _ r => B+A*(r+δ)+D*r^m)
    (fun _ => by unfold coldOpticalDepth; fun_prop)
    (fun _ => coldOpticalDepth_derivative B A δ D m) hν
  simpa only [coldOpticalDepth_zero,zero_sub] using h

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Cold survival for the actual capped periodic mild solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_survival {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-coldOpticalDepth
        (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
        (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t)*
        color s₀ η K α γ d₀ q N i p ≤
          rebuilt s₀ η K α γ d₀ q b L T N F.value i (t,JetBarrier.flight t p) := by
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (j) (p) : 0 ≤ color s₀ η K α γ d₀ q N j p ∧ color s₀ η K α γ d₀ q N j p ≤ R :=
    ⟨(hi.1 j p).1,(hi.1 j p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss F.measurable_value
    (measurable_color s₀ η K α γ d₀ q N) F.value_bounds hc₀ hi.2 (F.all_mild hT)
  have hc (j) (z) : 0 ≤ rebuilt s₀ η K α γ d₀ q b L T N F.value j z ∧
      rebuilt s₀ η K α γ d₀ q b L T N F.value j z ≤ R := by
    refine ⟨(hp.2.1 j z).1,?_⟩
    have hd := hp.2.2.1 {j} z
    simpa only [Finset.sum_singleton,rebuilt] using hd.trans (F.value_bounds z).2
  apply survival_of_capped_family hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hTmax hq hb hR hδ.le hsmall hloss m N i hi0 hwidth hdmax
    F.measurable_value hp.1 F.value_bounds hc (hp.2.2.2.2 i)
    (fun z => (hp.2.2.2.1 z).1)
    (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun z => (F.value_bounds z).1))
    (fun r hr j p => rebuilt_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hb hL hT hR (hTmax.trans (by norm_num)) hloss N hh₀ F.measurable_value
      F.value_bounds hF₀ j hr p)
    (PeriodicMildState.hot_bound_of_cap hq hb hL hT hR hδ hloss
      ((measurable_seed s₀ η K α γ d₀ q N).add hh₀m) hF₀
      (measurable_color s₀ η K α γ d₀ q N) hc₀ hi.2 F hcap) ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cold colors lie between their surviving free flight and the Gaussian excess -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def freeColor (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : Label) (t : ℝ)
    (p : JetPrototype.Phase) : ℝ :=
  color s₀ η K α γ d₀ q N i (JetBarrier.flight (-t) p)

theorem measurable_freeColor (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : Label) (t : ℝ) :
    Measurable (freeColor s₀ η K α γ d₀ q N i t) :=
  (measurable_color s₀ η K α γ d₀ q N i).comp
    ((GaussianLocal.measurable_flight).comp (measurable_const.prodMk measurable_id))

theorem freeColor_along (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : Label) (t : ℝ)
    (p : JetPrototype.Phase) :
    freeColor s₀ η K α γ d₀ q N i t (JetBarrier.flight t p) = color s₀ η K α γ d₀ q N i p := by
  simp only [freeColor,JetFreeTransport.neg_flight]

theorem physical_freeColor {s₀ η K α γ d₀ q : ℝ} {N : ℕ} {i : Label}
    (hi : i.annulus < N) (t : ℝ) (p : JetPrototype.Phase) :
    H q p.2*freeColor s₀ η K α γ d₀ q N i t p =
      JetFreeTransport.free η K α γ (jetScale s₀ η i.annulus)
        (d₀*jetScale s₀ η i.annulus^10) t i.positive (shift (displacement i.lattice) p) := by
  have he : shift (displacement i.lattice) (JetBarrier.flight (-t) p) =
      JetBarrier.flight (-t) (shift (displacement i.lattice) p) :=
    shift_flight _ _ _
  simp only [freeColor,color,ite_eq_left hi,JetDatum.term,JetBarrier.flight,shift] at *
  rw [mul_div_cancel₀ _ (H_pos q p.2).ne']
  exact congrArg (JetPrototype.density η K α γ (jetScale s₀ η i.annulus)
    (d₀*jetScale s₀ η i.annulus^10) i.positive) he

theorem rebuilt_le_free_add_barrier {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hTmax : T ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (i : Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F i (t,p) ≤
      H q p.2*freeColor s₀ η K α γ d₀ q N i t p+
        JetSupersolution.epsilon K (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10)*
          JetBarrier.barrier η K α γ (jetScale s₀ η i.annulus)
            (d₀*jetScale s₀ η i.annulus^10) t i.positive (shift (displacement i.lattice) p) := by
  by_cases hi : i.annulus < N
  · have h := rebuilt_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hb hL hT hR hTmax hloss N hh₀ hFm hF hF₀ i ht p
    rw [physical_freeColor hi]
    exact h
  · rw [rebuilt_zero s₀ η K α γ d₀ q b L T N (fun z => (hF z).1) i hi]
    simp only [Pi.zero_apply,mul_zero,freeColor,color,ite_eq_right hi,zero_add]
    have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
    have hd : 0 < d₀*jetScale s₀ η i.annulus^10 := by positivity
    exact mul_nonneg (JetSupersolution.epsilon_nonneg hK hs hd)
      (JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t i.positive _)

theorem eulerian_survival {s₀ η K α γ d₀ q b L T t E : ℝ} {N : ℕ} {i : Label}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (h : ∀ᵐ p ∂FlightMeasure.phaseVolume, Real.exp (-E)*color s₀ η K α γ d₀ q N i p ≤
      rebuilt s₀ η K α γ d₀ q b L T N F i (t,JetBarrier.flight t p)) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-E)*(H q p.2*freeColor s₀ η K α γ d₀ q N i t p) ≤
        H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F i (t,p) := by
  have he := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae h
  filter_upwards [he] with p hp
  simp only [JetFreeTransport.flight_neg] at hp
  have hm := mul_le_mul_of_nonneg_left hp (H_nonneg q p.2)
  simpa only [freeColor,mul_left_comm] using hm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform zero-hot control after a.e. pasting and cold reconstruction -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_zero_hot_bound (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R D : ℝ} (m : ℕ)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hD : 0 ≤ D)
    (hBD : (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ)) ≤ D)
    (hquad : (2*HotApplication.realBound q)*D*T ≤ 1)
    (hm : 2*JetMainGain.coefficient K α γ q+2 ≤ (m+1 : ℕ))
    (htail : JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent (m+1 : ℕ))*T^(m+1) ≤ 1)
    (N : ℕ) {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N (fun _ => 0) p ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N (fun _ => 0)) (forcing q b L F) (t,p)))
    (hclamp : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (hperiodic : ∀ n, pull (displacement n) F = F) :
    ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p =>
      F (t,p)-∑' i, rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ D*t^(m+1) := by
  let c := rebuilt s₀ η K α γ d₀ q b L T N F
  let h (u : ℝ × JetPrototype.Phase) := F u-∑' i, c i u
  let g := remainderForcing q b L F c
  let S := HotApplication.realBound q*R^2+L*R
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N
    (fun _ => le_rfl : ∀ _ : JetPrototype.Phase, (0:ℝ) ≤ 0)
  have hcb (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧ color s₀ η K α γ d₀ q N i p ≤ R :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hcb hi.2 hFeq
  have hcm (i) : Measurable (c i) := hp.1 i
  have hcn (i) (u) : 0 ≤ c i u := (hp.2.1 i u).1
  have hsum (s : Finset JetLattice.Label) (u) : ∑ i ∈ s, c i u ≤ F u := hp.2.2.1 s u
  have hr := family_hot_bounds hq₂ hb hR hloss hFm hcm hF hcn hsum
  have hgain : 0 < HotApplication.realBound q := HotApplication.realBound_pos q
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hge (u) : 0 ≤ g u ∧ g u ≤ S := hr.2.2.2 u
  have hga (u) : |g u| ≤ S := by rw [abs_of_nonneg (hge u).1]; exact (hge u).2
  have hhe : ∀ t ∈ Icc 0 T, (fun p => h (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (fun _ => 0) g (t,p)) := by
    have hh := family_hot_mildAE hq₂ hb hL hT hR hloss hFm hcm hF hcn hsum
      (fun i p => (hi.1 i p).1) hi.2 (fun t _ => hFeq t) hp.2.2.2.2
    simpa only [initial,seed,add_zero,sub_self] using hh
  have hhc (u : ℝ × JetPrototype.Phase) : h (PositiveIntegral.time T u.1,u.2) = h u := by
    dsimp only [h]
    rw [hclamp u]
    congr 1
    apply tsum_congr
    intro i
    exact rebuiltColdFamily_time_clamp hT q b L hclamp _ i u
  have hnorm : Continuous (fun t => PhaseEssSup.size (fun p => h (t,p))) :=
    PhaseEssSup.continuous_size_of_mildAE hT hL (le_rfl : (0:ℝ) ≤ 0) hS
      measurable_const hr.2.2.1 (fun _ => ⟨le_rfl,le_rfl⟩) hge
      (mild_all_of_time_clamp hT L hhc hhe)
  have hE := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α
    (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hsource := geometric_hot_norm_source (b := b) hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hL hTmax (m+1 : ℕ) N hFm hcm hF hcn hsum
    (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun u => (hF u).1))
    (fun t ht i x w => rebuilt_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall hq₂ hb
      hL hT hR (hTmax.trans (by norm_num)) hloss N (fun _ => le_rfl) hFm hF hF₀ i ht
        (JetPeriodicDatum.spatialMap x,w))
    hperiodic (fun n i => rebuilt_shift n (hperiodic n) i) hnorm.measurable (by
      intro t ht
      rw [Real.rpow_natCast]
      exact tail_small hE ht.1.le ht.2 htail)
  have hM : 0 ≤ 2*JetMainGain.coefficient K α γ q :=
    mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q)
  have hC : 0 ≤ 2*HotApplication.realBound q := mul_nonneg (by norm_num) hgain.le
  have hB : 0 ≤ (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ)) :=
    mul_nonneg (add_nonneg hM hC) hE
  apply PhaseEssSup.zero_seed_bound_ae hT (hTmax.trans (by norm_num)) hL hR hM hC hB hBD hD
    (DatumBounds.scale_pos hs₀ (N+1)) hquad hm hr.2.2.1 hr.1 hga hr.2.1 hnorm.continuousOn
    (ae_of_all _ (fun _ => le_rfl)) hhe
  filter_upwards [hsource] with u hu ht
  have hh := hu ht
  rw [scalarMajorant_eq_source s₀ η K α γ d₀ q N m ht.1] at hh
  exact hh

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Local free-transport error for the actual capped periodic solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_local_free_error {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
    (hi : i.annulus < N) (Ω : Set JetPrototype.Space)
    [IsFiniteMeasure (JetPrototype.spaceVolume.restrict Ω)]
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    let s := jetScale s₀ η i.annulus
    let E := coldOpticalDepth (4*JetBarrierCollision.frequencyConstant*K*d₀*s^9)
      (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t
    let ε := JetSupersolution.epsilon K s (d₀*s^10)
    let μ := (JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity)
    let error := fun p : JetPrototype.Phase =>
      |H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F.value i (t,p)-
        JetFreeTransport.free η K α γ s (d₀*s^10) t i.positive (shift (displacement i.lattice) p)|
    Integrable error μ ∧ (∫ p, error p ∂μ) ≤
      (E+ε)*(JetPrototype.spaceVolume.restrict Ω).real univ*(JetBarrierLocalMass.massConstant*(K/s)) := by
  dsimp only
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hd : 0 < d₀*jetScale s₀ η i.annulus^10 := by positivity
  have hT₁ : T ≤ 1 := hTmax.trans (by norm_num)
  have hinit := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (j) (p) : 0 ≤ color s₀ η K α γ d₀ q N j p ∧ color s₀ η K α γ d₀ q N j p ≤ R :=
    ⟨(hinit.1 j p).1,(hinit.1 j p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss F.measurable_value
    (measurable_color s₀ η K α γ d₀ q N) F.value_bounds hc₀ hinit.2 (F.all_mild hT)
  have hcm : Measurable (fun p : JetPrototype.Phase =>
      H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F.value i (t,p)) :=
    ((ChartKernel.measurable_H q).comp measurable_snd).mul
      ((hp.1 i).comp (measurable_const.prodMk measurable_id))
  have hl := eulerian_survival (rebuilt_survival hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hTmax hq hb hL hT hR hδ hsmall hloss m N i hi0 hwidth hdmax
    hh₀m hh₀ hF₀ F hcap ⟨ht.1.le,ht.2⟩)
  have hac : (JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity) ≪
      FlightMeasure.phaseVolume :=
    Measure.absolutelyContinuous_restrict.prod Measure.AbsolutelyContinuous.rfl
  have hl' := hl.filter_mono hac.ae_le
  simp_rw [physical_freeColor hi] at hl'
  have hE : 0 ≤ coldOpticalDepth
      (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
      (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t := by
    apply coldOpticalDepth_nonneg _ (weightFrequencyConstant_nonneg q (by norm_num)) hδ.le
      (escapedFrequencyConstant_nonneg hs₀ hK hd₀ η α q m) ht.1.le
    have := JetBarrierCollision.frequencyConstant_nonneg
    positivity
  apply JetLocalFreeError.integral_error_le hK hα hγ hs hd ht.1 (ht.2.trans hT₁) hE
    (JetSupersolution.epsilon_nonneg hK hs hd) η i.positive (displacement i.lattice)
    (JetPrototype.spaceVolume.restrict Ω) hcm hl'
  exact ae_of_all _ (fun p => by
    have hu := rebuilt_le_free_add_barrier hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hb hL hT hR hT₁ hloss N hh₀ F.measurable_value F.value_bounds hF₀ i ht p
    simpa only [physical_freeColor hi,jetScale] using hu)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A time independent of the truncation controls every zero-seed local solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_rebuilt_zero_control (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧
      ∀ (N : ℕ) (b L T R : ℝ), 0 ≤ b → 0 ≤ L → 0 ≤ T → T ≤ τ → 0 ≤ R →
        R*CutoffLipschitz.frequencyConstant q b ≤ L →
        ∀ F : ℝ × JetPrototype.Phase → ℝ, Measurable F →
          (∀ u, 0 ≤ F u ∧ F u ≤ R) →
          (∀ p, initial s₀ η K α γ d₀ q N (fun _ => 0) p ≤ R) →
          (∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
            (fun p => PositiveIntegral.value T L JetBarrier.flight
              (initial s₀ η K α γ d₀ q N (fun _ => 0)) (forcing q b L F) (t,p))) →
          (∀ u, F (PositiveIntegral.time T u.1,u.2) = F u) →
          (∀ n, pull (displacement n) F = F) →
          ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p =>
            F (t,p)-∑' i, rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ t^2 := by
  let M := 2*JetMainGain.coefficient K α γ q
  let C := 2*HotApplication.realBound q
  let E (m : ℕ) := JetEscapedEnvelope.constant s₀ η α K d₀
    (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le
  have hE (m : ℕ) : 0 ≤ E m := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  obtain ⟨m,D,τ,hm₂,hD,hτ,hτmax,hm,hBD,hquad,htail,hDτ⟩ :=
    ZeroProfile.parameters_exist hM hC E hE
  refine ⟨τ,hτ,hτmax,?_⟩
  intro N b L T R hb hL hT hTτ hR hloss F hFm hF hF₀ hFeq hclamp hperiodic t ht
  have hquadT : C*D*T ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTτ (mul_nonneg hC hD.le)).trans hquad
  have htailT : E m*T^(m+1) ≤ 1 :=
    tail_small (hE m) hT hTτ htail
  have hz := rebuilt_zero_hot_bound hcarleman m hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq₁ hq₂ hb hL hT hR (hTτ.trans hτmax) hloss hD.le hBD hquadT hm htailT N
    hFm hF hF₀ hFeq hclamp hperiodic t ht
  exact hz.trans (ZeroProfile.profile_le_square hD.le
    ((hTτ.trans hτmax).trans (by norm_num))
    ((mul_le_mul_of_nonneg_left hTτ hD.le).trans hDτ) hm₂ ht)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Constructed zero-hot approximations on a uniform positive time interval -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def continuationAmplitude (s₀ η K α d₀ : ℝ) (N : ℕ) : ℝ :=
  WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N+1

theorem exists_uniform_zero_solution (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ (N : ℕ) (b : ℝ), 0 ≤ b →
      ∃ F : PeriodicMildState q b (damping q b (continuationAmplitude s₀ η K α d₀ N))
        τ (2*continuationAmplitude s₀ η K α d₀ N) (initial s₀ η K α γ d₀ q N (fun _ => 0)),
        ∀ t ∈ Icc 0 τ, PhaseEssSup.size (fun p => F.value (t,p)-
          ∑' i, rebuilt s₀ η K α γ d₀ q b (damping q b (continuationAmplitude s₀ η K α d₀ N))
            τ N F.value i (t,p)) ≤ t^2 := by
  have hαone : α ≤ 1 := hαmax.trans (by norm_num)
  obtain ⟨τ,hτ,hτmax,hcontrol⟩ := exists_uniform_rebuilt_zero_control hcarleman hs₀ hsmax hη hηmax
    hK hα hαone hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨τ,hτ,hτmax,?_⟩
  intro N b hb
  let A := continuationAmplitude s₀ η K α d₀ N
  let f₀ := initial s₀ η K α γ d₀ q N (fun _ => 0)
  have hamp : 0 < WeightedFiniteSeed.amplitude s₀ η K d₀ N :=
    WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N
  have hcold : 0 ≤ coldNormBound s₀ η K α d₀ N := coldNormBound_nonneg hs₀ hK hd₀ η α N
  have hA : 0 < A := by dsimp [A,continuationAmplitude]; linarith
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  have hf₀m : Measurable f₀ := (measurable_seed s₀ η K α γ d₀ q N).add measurable_const
  have hf₀ (p) : 0 ≤ f₀ p ∧ f₀ p ≤ A := by
    have h := seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα.le hαmax γ q N p
    constructor
    · simpa only [f₀,initial,add_zero] using h.1
    · change seed s₀ η K α γ d₀ q N p+0 ≤ A
      dsimp [A,continuationAmplitude]
      linarith [h.2]
  have hf₀R (p) : f₀ p ≤ 2*A := (hf₀ p).2.trans (by linarith)
  have hfper (n) (p) : f₀ (shift (displacement n) p) = f₀ p := by
    simp only [f₀,initial,add_zero,seed_periodic]
  have hapriori (T : ℝ) (hT : 0 ≤ T) (hTτ : T ≤ τ)
      (F : PeriodicMildState q b (damping q b A) T (2*A) f₀) :
      ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (T,p) ≤ A := by
    by_cases hTzero : T = 0
    · subst T
      filter_upwards [F.mild 0 ⟨le_rfl,le_rfl⟩] with p hp
      have he : PositiveIntegral.value 0 (damping q b A) JetBarrier.flight f₀
          (forcing q b (damping q b A) F.value) (0,p) = f₀ p := by
        simp [PositiveIntegral.value,PositiveIntegral.time,JetBarrier.flight]
      rw [he] at hp
      exact hp.le.trans (hf₀ p).2
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
      have hz := hcontrol N b (damping q b A) T (2*A) hb hL hT hTτ hR hloss
        F.value F.measurable_value F.value_bounds hf₀R (F.all_mild hT) F.clamped F.periodic T ⟨hT,le_rfl⟩
      have hn := rebuilt_total_norm_le hs₀ hsmax hη hηmax hK hα.le hαone hγ.le hd₀ hd₀max hsmall
        hq₂ hb hL hT hR (hTτ.trans hτmax) hloss N (fun _ => le_rfl) F.measurable_value
        F.value_bounds hf₀R (F.all_mild hT) F.periodic ⟨hTpos,le_rfl⟩ hz
      have hnA : PhaseEssSup.size (fun p => F.value (T,p)) ≤ A := by
        have ht1 : T ≤ 1 := (hTτ.trans hτmax).trans (by norm_num)
        dsimp [A,continuationAmplitude]
        nlinarith [sq_nonneg T]
      have hae := PhaseEssSup.ae_abs_le_size
        (F.measurable_value.comp (measurable_const.prodMk measurable_id))
        (fun p => show |F.value (T,p)| ≤ 2*A from by
          rw [abs_of_nonneg (F.value_bounds (T,p)).1]
          exact (F.value_bounds (T,p)).2)
      filter_upwards [hae] with p hp
      exact (le_abs_self _).trans (hp.trans hnA)
  obtain ⟨F⟩ := exists_to_time_of_apriori hq₂ hb hA hτ.le hf₀m hf₀ hfper hapriori
  refine ⟨F,?_⟩
  exact hcontrol N b (damping q b A) τ (2*A) hb hL hτ.le le_rfl hR hloss
    F.value F.measurable_value F.value_bounds hf₀R (F.all_mild hτ.le) F.clamped F.periodic

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Zero-hot construction with any sufficiently large common amplitude -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_zero_solution_large (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ (N : ℕ) (b A T : ℝ), 0 ≤ b →
      continuationAmplitude s₀ η K α d₀ N ≤ A → 0 ≤ T → T ≤ τ →
      ∃ F : PeriodicMildState q b (damping q b A)
        T (2*A) (initial s₀ η K α γ d₀ q N (fun _ => 0)),
        ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p => F.value (t,p)-
          ∑' i, rebuilt s₀ η K α γ d₀ q b (damping q b A)
            T N F.value i (t,p)) ≤ t^2 := by
  have hαone : α ≤ 1 := hαmax.trans (by norm_num)
  obtain ⟨τ,hτ,hτmax,hcontrol⟩ := exists_uniform_rebuilt_zero_control hcarleman hs₀ hsmax hη hηmax
    hK hα hαone hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨τ,hτ,hτmax,?_⟩
  intro N b A T hb hAle hT hTτ
  let f₀ := initial s₀ η K α γ d₀ q N (fun _ => 0)
  have hamp : 0 < WeightedFiniteSeed.amplitude s₀ η K d₀ N :=
    WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N
  have hcold : 0 ≤ coldNormBound s₀ η K α d₀ N := coldNormBound_nonneg hs₀ hK hd₀ η α N
  have hA : 0 < A := by
    unfold continuationAmplitude at hAle
    linarith
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  have hf₀m : Measurable f₀ := (measurable_seed s₀ η K α γ d₀ q N).add measurable_const
  have hf₀ (p) : 0 ≤ f₀ p ∧ f₀ p ≤ A := by
    have h := seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα.le hαmax γ q N p
    constructor
    · simpa only [f₀,initial,add_zero] using h.1
    · change seed s₀ η K α γ d₀ q N p+0 ≤ A
      unfold continuationAmplitude at hAle
      linarith [h.2]
  have hf₀R (p) : f₀ p ≤ 2*A := (hf₀ p).2.trans (by linarith)
  have hfper (n) (p) : f₀ (shift (displacement n) p) = f₀ p := by
    simp only [f₀,initial,add_zero,seed_periodic]
  have hapriori (S : ℝ) (hS : 0 ≤ S) (hST : S ≤ T)
      (F : PeriodicMildState q b (damping q b A) S (2*A) f₀) :
      ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (S,p) ≤ A := by
    have hSτ : S ≤ τ := hST.trans hTτ
    by_cases hTzero : S = 0
    · subst S
      filter_upwards [F.mild 0 ⟨le_rfl,le_rfl⟩] with p hp
      have he : PositiveIntegral.value 0 (damping q b A) JetBarrier.flight f₀
          (forcing q b (damping q b A) F.value) (0,p) = f₀ p := by
        simp [PositiveIntegral.value,PositiveIntegral.time,JetBarrier.flight]
      rw [he] at hp
      exact hp.le.trans (hf₀ p).2
    · have hTpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hTzero)
      have hz := hcontrol N b (damping q b A) S (2*A) hb hL hS hSτ hR hloss
        F.value F.measurable_value F.value_bounds hf₀R (F.all_mild hS) F.clamped F.periodic S ⟨hS,le_rfl⟩
      have hn := rebuilt_total_norm_le hs₀ hsmax hη hηmax hK hα.le hαone hγ.le hd₀ hd₀max hsmall
        hq₂ hb hL hS hR (hSτ.trans hτmax) hloss N (fun _ => le_rfl) F.measurable_value
        F.value_bounds hf₀R (F.all_mild hS) F.periodic ⟨hTpos,le_rfl⟩ hz
      have hnA : PhaseEssSup.size (fun p => F.value (S,p)) ≤ A := by
        have ht1 : S ≤ 1 := (hSτ.trans hτmax).trans (by norm_num)
        unfold continuationAmplitude at hAle
        nlinarith [sq_nonneg S]
      have hae := PhaseEssSup.ae_abs_le_size
        (F.measurable_value.comp (measurable_const.prodMk measurable_id))
        (fun p => show |F.value (S,p)| ≤ 2*A from by
          rw [abs_of_nonneg (F.value_bounds (S,p)).1]
          exact (F.value_bounds (S,p)).2)
      filter_upwards [hae] with p hp
      exact (le_abs_self _).trans (hp.trans hnA)
  obtain ⟨F⟩ := exists_to_time_of_apriori hq₂ hb hA hT hf₀m hf₀ hfper hapriori
  refine ⟨F,?_⟩
  exact hcontrol N b (damping q b A) T (2*A) hb hL hT hTτ hR hloss
    F.value F.measurable_value F.value_bounds hf₀R (F.all_mild hT) F.clamped F.periodic

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
