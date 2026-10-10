import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedNonaxialLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.RescaledColdMajorant

namespace OAI

/-! # Velocity measurability and measure domination for the actual selected remainder -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selectedRemainderDensity_measurable_velocity {s₀ η : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (r K α γ : ℝ) {d₀ : ℝ} (hd₀ : 0 < d₀) (N : ℕ) (x : SpaceTime) :
    Measurable (fun v => selectedRemainderDensity r s₀ η K α γ d₀ N (x,v)) := by
  classical
  by_cases hmain : ∃ i, x ∈ mainCoreRegion s₀ η r N i
  · obtain ⟨i,hi⟩ := hmain
    have he : (fun v => selectedRemainderDensity r s₀ η K α γ d₀ N (x,v)) =
        (fun v => copyRemainderDensity r s₀ η K α γ d₀ i (x,v)) :=
      funext (fun _ => selectedRemainderDensity_eq hs₀ hsmax hη hηmax K α γ d₀ hi)
    rw [he]
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    exact measurable_const.mul ((measurable_const.mul
      (JetBarrierCollision.measurable_velocity (by positivity) η K α γ
        (JetGeometry.jetScale s₀ η i.annulus) (r*x.1) i.positive
        (JetPeriodicDatum.spatialMap (r • x.2)-displacement i.lattice))).ennreal_ofReal)
  · have he : (fun v => selectedRemainderDensity r s₀ η K α γ d₀ N (x,v)) = 0 :=
      funext (fun _ => selectedRemainderDensity_eq_zero _ _ _ _ _ _ _ _ _
        (fun i hi => hmain ⟨i,hi⟩))
    rw [he]
    exact measurable_const

theorem CapApproximation.rescaled_cold_measure_majorant {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T) :
    volume.withDensity (fun v => ENNReal.ofReal (r*(H q v*F.coldTotal
      (r*x.1,(JetPeriodicDatum.spatialMap (r • x.2),v))))) ≤
      selectedColdKernel r s₀ η K α γ d₀ N x+
      volume.withDensity (fun v => selectedRemainderDensity r s₀ η K α γ d₀ N (x,v))+
      volume.withDensity (fun v => ENNReal.ofReal
        (r*(H q v*F.escapedTotal ((r*x.1,r • x.2),v)))) := by
  rw [selectedColdKernel_density,← withDensity_add_left,← withDensity_add_left]
  · apply withDensity_mono
    exact ae_of_all _ (fun v => F.rescaled_cold_majorant hr hs₀ hsmax hη hηmax hK hα hγ hd₀
      hsmall hq hT hTmax (x,v) ht)
  · exact ((selectedCoreDensity_measurable r s₀ η K α γ d₀ N).comp
      (measurable_const.prodMk measurable_id)).add
      (selectedRemainderDensity_measurable_velocity hs₀ hsmax hη hηmax r K α γ hd₀ N x)
  · exact (selectedCoreDensity_measurable r s₀ η K α γ d₀ N).comp
      (measurable_const.prodMk measurable_id)

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
