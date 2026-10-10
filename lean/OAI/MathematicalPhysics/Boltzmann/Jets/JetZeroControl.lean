import OAI.MathematicalPhysics.Boltzmann.Branching.HotRatioCollisionTrace
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotRegularity
import OAI.MathematicalPhysics.Boltzmann.Branching.ZeroProfileParameters
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds

namespace OAI

section

/-! # Uniform zero-seed control for the actual periodic local approximation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem zero_hot_bound (hcarleman : Published.GPV2009CarlemanInput)
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
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N (fun _ => 0)) (forcing q b L F) u)
    (hperiodic : ∀ n, pull (displacement n) F = F) :
    ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p =>
      hotRemainder q b L T F (color s₀ η K α γ d₀ q N) (t,p)) ≤ D*t^(m+1) := by
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N
    (fun _ => le_rfl : ∀ _ : JetPrototype.Phase, (0:ℝ) ≤ 0)
  have hs := hotRemainder_solution hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hi.1 hF₀ hi.2 hFeq
  have hr := hot_regularity hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hi.1 hF₀ hi.2 hFeq
  have hE := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α
    (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hsource := hot_source_norm_bound hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq₁ hq₂ hb hL hT hR hTmax hloss (m+1 : ℕ) N (fun _ => le_rfl)
    hFm hF hF₀ hFeq hperiodic hr.2.2.measurable (by
      intro t ht
      rw [Real.rpow_natCast]
      exact tail_small hE ht.1.le ht.2 htail)
  have hM : 0 ≤ 2*JetMainGain.coefficient K α γ q :=
    mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q)
  have hC : 0 ≤ 2*HotApplication.realBound q :=
    mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le
  have hB : 0 ≤ (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ)) :=
    mul_nonneg (add_nonneg hM hC) hE
  have hgain : 0 < HotApplication.realBound q := HotApplication.realBound_pos q
  apply PhaseEssSup.zero_seed_bound hT (hTmax.trans (by norm_num)) hL
    (show 0 ≤ HotApplication.realBound q*R^2+L*R by positivity) hR hM hC hB hBD hD
    (DatumBounds.scale_pos hs₀ (N+1)) hquad hm hr.1 hs.1 hr.2.1
    (fun u => ⟨(hs.2.1 u).1,(hs.2.1 u).2.trans (hF u).2⟩)
    (ae_of_all _ (by intro p; simp [initial,seed])) hs.2.2.2
  filter_upwards [hsource] with u hu ht
  have hh := hu ht
  rw [scalarMajorant_eq_source s₀ η K α γ d₀ q N m ht.1] at hh
  exact hh

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A time independent of the truncation controls every zero-seed local solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_zero_control (hcarleman : Published.GPV2009CarlemanInput)
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
          (∀ u, F u = PositiveIntegral.value T L JetBarrier.flight
            (initial s₀ η K α γ d₀ q N (fun _ => 0)) (forcing q b L F) u) →
          (∀ n, pull (displacement n) F = F) →
          ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p =>
            hotRemainder q b L T F (color s₀ η K α γ d₀ q N) (t,p)) ≤ t^2 := by
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
  intro N b L T R hb hL hT hTτ hR hloss F hFm hF hF₀ hFeq hperiodic t ht
  have hquadT : C*D*T ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTτ (mul_nonneg hC hD.le)).trans hquad
  have htailT : E m*T^(m+1) ≤ 1 :=
    tail_small (hE m) hT hTτ htail
  have hz := zero_hot_bound hcarleman m hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq₁ hq₂ hb hL hT hR (hTτ.trans hτmax) hloss hD.le hBD hquadT hm htailT N
    hFm hF hF₀ hFeq hperiodic t ht
  exact hz.trans (ZeroProfile.profile_le_square hD.le
    ((hTτ.trans hτmax).trans (by norm_num))
    ((mul_le_mul_of_nonneg_left hTτ hD.le).trans hDτ) hm₂ ht)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
