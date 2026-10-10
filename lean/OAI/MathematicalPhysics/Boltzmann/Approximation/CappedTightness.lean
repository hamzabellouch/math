import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence
import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffLossFrequency
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularTightness

namespace OAI

section

/-! # Uniform gain and loss integrability for the actual capped approximation family -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_family_gainLoss_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
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
    UniformIntegrable (fun n => CollisionCompactness.gainDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun n => CollisionCompactness.lossDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  apply CollisionCompactness.annular_gainLoss_uniformIntegrable hs₀ hη hηmax hT hq
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

/-! # Uniform integrability of collision terms in the constructed cap sequence -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_family_gainLoss_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, CapApproximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.gainDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.lossDensity (torusPhysical q (F N).solution.value)) 1
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
  exact capped_family_gainLoss_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap.le)

theorem cap_family_cutoff_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, CapApproximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1) (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1) (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hp := cap_family_pairs_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax F
  have hc := cap_family_gainLoss_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax F
  exact CollisionCompactness.cutoff_gainLoss_uniformIntegrable
    (fun (N : ℕ) => torusPhysical_measurable (F N).solution.measurable_value q)
    (fun (N : ℕ) => torusPhysical_nonneg (fun z => ((F N).solution.value_bounds z).1) q)
    (fun (N : ℕ) => memLp_one_iff_integrable.mp (hp.memLp N)) hc.1 hc.2 (fun (N : ℕ) => N+1)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Tightness of the actual capped approximation family -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_family_unifTight {s₀ η K α γ d₀ q T : ℝ}
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
    UnifTight (fun n => torusPhysical q (F n).value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => CollisionCompactness.pairDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
    UnifTight (fun n => CollisionCompactness.gainDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => CollisionCompactness.lossDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  apply CollisionCompactness.annular_unifTight hs₀ hη hηmax hT hq
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

theorem cap_family_unifTight {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, CapApproximation s₀ η K α γ d₀ q T N) :
    UnifTight (fun N => torusPhysical q (F N).solution.value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun N => CollisionCompactness.pairDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
    UnifTight (fun N => CollisionCompactness.gainDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun N => CollisionCompactness.lossDensity (torusPhysical q (F N).solution.value)) 1
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
  exact capped_family_unifTight hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
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
