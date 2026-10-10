import OAI.MathematicalPhysics.Boltzmann.Approximation.CapCoefficientExtraction
import OAI.MathematicalPhysics.Boltzmann.Approximation.DormantConstruction
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

/-! # Equality of strong time representatives implies equality of weak densities -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness

theorem kineticDensity_agreement {T : ℝ} {F G : Evolution}
    (hF : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hG : Measurable (fun z : ℝ × Phase => G z.1 z.2))
    (h : ∀ t ∈ Icc 0 T, F t =ᵐ[volume] G t) :
    kineticDensity F =ᵐ[(AnnularEnvelope.timePositionVolume T).prod volume] kineticDensity G := by
  have he : (fun z : ℝ × Phase => F z.1 z.2) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume] (fun z => G z.1 z.2) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hG)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact h t ht
  exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae he

namespace JetCopyDatum

theorem CapLocalLimit.density_eq_dormant {s₀ η K α γ d₀ q : ℝ}
    {A : TightCapFamily s₀ η K α γ d₀ q} (L : CapLocalLimit A)
    {B : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit B) (hT : A.time ≤ B.time)
    (h : ∀ t ∈ Icc 0 A.time,
      MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) L.density t
        =ᵐ[volume]
      MildCollisionSolution.positiveEvolution B.time (JetPeriodicDatum.datum s₀ η K α γ d₀) D.density t) :
    L.density =ᵐ[(AnnularEnvelope.timePositionVolume A.time).prod volume] D.density := by
  have he := kineticDensity_agreement L.admissible.measurable D.admissible.measurable h
  have hd : D.density =ᵐ[(AnnularEnvelope.timePositionVolume A.time).prod volume]
      kineticDensity (MildCollisionSolution.positiveEvolution B.time
        (JetPeriodicDatum.datum s₀ η K α γ d₀) D.density) :=
    ae_mono (Measure.prod_mono (timePositionVolume_mono hT) le_rfl) D.mild.positiveDensity_eq_ae
  exact L.mild.positiveDensity_eq_ae.trans (he.trans hd.symm)

end JetCopyDatum
end BoltzmannNonuniqueness

end

end OAI
