import OAI.Analysis.CircleDomains.Selection.ScalarBoundedRepresentative
import OAI.Analysis.CircleDomains.Sobolev.LocalizedSobolevRange

namespace OAI

/-! The local range principle applied to the actual scalar weak limit. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem le_on_cutoff_plateau (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hunit : ∀ x, η x ∈ Icc 0 1)
    (hηd : ∀ x, complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) → fderiv ℝ η x = 0)
    {b : ℝ} (hb : 0 ≤ b)
    (hrange : ∀ x, complexPlaneCoordinates x ∈
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      η x ≠ 0 → R.imageScalar i (complexPlaneCoordinates x) ≤ b) :
    ∀ᵐ x ∂volume, η x = 1 → W.scalar (complexPlaneCoordinates x) ≤ b := by
  have he := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.eq_source_ae R hsch hG)
  have h := localized_sobolev_range W.boundedRepresentative_measurable
    W.boundedRepresentative_unit W.planarWeakGradient_memLp W.boundedRepresentative_weak
    (D := complexPlaneCoordinates ⁻¹'
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)))
    (W.planarWeakGradient_zero_off_image hsch hG) hη hs hunit hηd hb (by
      filter_upwards [he, W.boundedRepresentative_ae] with x hx hrep hxin hηx
      rw [hrep]
      change W.scalar (complexPlaneCoordinates x) ≤ b
      rw [hx hxin]
      exact hrange x hxin hηx)
  filter_upwards [h, W.boundedRepresentative_ae] with x hx hrep hηx
  have ht := hx hηx
  rwa [hrep] at ht

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
