import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedTightness
import OAI.MathematicalPhysics.Boltzmann.Branching.CompactCapFamily

namespace OAI

/-! # Constructed cap families with uniform tightness in velocity -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

structure TightCapFamily (s₀ η K α γ d₀ q : ℝ) extends CompactCapFamily s₀ η K α γ d₀ q where
  density_tight : UnifTight (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_tight : UnifTight (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_tight : UnifTight (fun N => CollisionCompactness.gainDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_tight : UnifTight (fun N => CollisionCompactness.lossDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))

theorem exists_tight_cap_family (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    Nonempty (TightCapFamily s₀ η K α γ d₀ q) := by
  obtain ⟨F⟩ := exists_compact_cap_family hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hwidth hsmall hq₁ hq₂
  have ht := cap_family_unifTight hs₀ hsmax hη hηmax hK hα (hαmax.trans (by norm_num))
    hγ hd₀ hd₀max hsmall hq₂ F.time_pos.le F.time_le F.approximation
  exact ⟨⟨F,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
