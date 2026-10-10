import OAI.Analysis.CircleDomains.Sobolev.SmoothImageScalar
import OAI.Analysis.CircleDomains.Sobolev.SmoothLocalWeakDerivative

namespace OAI

/-! The two weak fields of the actual limit are the ordinary smooth
partials on its open conformal image. -/
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

 theorem gradient_on_image (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      W.horizontal z = fderiv ℝ (R.imageScalar i) z 1 ∧
      W.vertical z = fderiv ℝ (R.imageScalar i) z Complex.I := by
  have hU := (R.limit.plane_open_embedding hG).2.1 _
    (hG.preimage OnePoint.continuous_coe) (Subset.refl _)
  have hs : ContDiffOn ℝ 1 (R.imageScalar i)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :=
    (R.imageScalar_contDiffOn hG i).of_le (by simp)
  have he := W.eq_source_ae R hsch hG
  have hx := weak_field_eq_smooth_derivative hU 1 hs (Lp.memLp W.horizontal) he
    (fun φ hφ hφs => (W.derivative φ hφ hφs).1)
  have hy := weak_field_eq_smooth_derivative hU Complex.I hs (Lp.memLp W.vertical) he
    (fun φ hφ hφs => (W.derivative φ hφ hφs).2)
  filter_upwards [hx, hy] with z hzx hzy hz
  exact ⟨hzx hz, hzy hz⟩

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
