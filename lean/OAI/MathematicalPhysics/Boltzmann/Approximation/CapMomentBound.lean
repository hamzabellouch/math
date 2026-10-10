import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotCapBound
import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotInitial
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Jets.JetContinuation

namespace OAI

section

/-! # Initial lower bounds and zero-seed strict upper bounds for the cap peak -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Cap

theorem peak_le_of_bound {T δ C : ℝ} {z : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hz : ContinuousOn z (Icc 0 T)) (hbound : ∀ t ∈ Icc 0 T, z t ≤ C*(t+δ)) :
    peak T δ z ≤ C := by
  obtain ⟨t,ht,he,_⟩ := peak_attained hT hδ hz
  rw [he]
  exact (div_le_iff₀ (by linarith [ht.1] : 0 < t+δ)).mpr (hbound t ht)

theorem peak_le_of_square {T δ : ℝ} {z : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hz : ContinuousOn z (Icc 0 T)) (hbound : ∀ t ∈ Icc 0 T, z t ≤ t^2) :
    peak T δ z ≤ T := by
  apply peak_le_of_bound hT hδ hz
  intro t ht
  have hp : t^2 ≤ T*(t+δ) := by
    nlinarith [mul_nonneg hT hδ.le,mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  exact (hbound t ht).trans hp

end BoltzmannNonuniqueness.Cap

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

open WeightedLocal

theorem hotPeak_ge_initial {I : Type*} [Countable I] {q b L T R δ : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F₀ : JetPrototype.Phase → ℝ} (hF₀m : Measurable F₀) (hF₀ : ∀ p, F₀ p ≤ R)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (F : PeriodicMildState q b L T R F₀) :
    PhaseEssSup.size (fun p => F₀ p-∑' i, c₀ i p)/δ ≤ hotPeak δ c₀ F := by
  have hi := rebuilt_hot_initial_ae hq hb hL hT hR hloss F.measurable_value hc₀m F.value_bounds hc₀ hdom
    (F.all_mild hT)
  have he := PhaseEssSup.size_congr_ae hi
  have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value hF₀m hc₀m
    F.value_bounds hF₀ hc₀ hdom (F.all_mild hT)
  obtain ⟨_,_,_,hpeak⟩ := Cap.peak_attained hT hδ hreg
  have h := hpeak 0 ⟨le_rfl,hT⟩
  simpa only [zero_add,he,hotPeak] using h

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # A truncation-independent moment envelope for the actual capped solutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem hot_size_le_cap {I : Type*} [Countable I] {q b L T R δ : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F₀ : JetPrototype.Phase → ℝ} (hF₀m : Measurable F₀) (hF₀ : ∀ p, F₀ p ≤ R)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (F : PeriodicMildState q b L T R F₀) (hcap : hotPeak δ c₀ F ≤ 1) :
    ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p => F.value (t,p)-
      ∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ t+δ := by
  have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value hF₀m hc₀m
    F.value_bounds hF₀ hc₀ hdom (F.all_mild hT)
  obtain ⟨_,_,_,hpeak⟩ := Cap.peak_attained hT hδ hreg
  intro t ht
  have hratio := (hpeak t ht).trans hcap
  exact (div_le_one (by linarith [ht.1] : 0 < t+δ)).mp hratio

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

namespace BoltzmannNonuniqueness.JetCopyDatum

open WeightedLocalControl

theorem capped_cell_moment {s₀ η K α γ d₀ q b L T R δ : ℝ}
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
    ∀ᵐ x : Velocity, x ∈ TorusChart.cube →
      moment (fun v => H q v*F.value (t,(JetPeriodicDatum.spatialMap x,v))) ≤ ENNReal.ofReal
        ((2+escapedConstant s₀ η K α d₀)*hotConstant q+
          JetEnvelopeGain.momentConstant K α γ*
            AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x)) := by
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
  exact rebuilt_cell_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
    hq hb hL hT hR hTmax (by norm_num) hloss N hh₀ F.measurable_value F.value_bounds hF₀
    (F.all_mild hT) ht hz2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
