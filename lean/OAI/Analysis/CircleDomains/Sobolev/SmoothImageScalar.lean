import OAI.Analysis.CircleDomains.Transfer.ScalarImageIdentification
import OAI.Analysis.CircleDomains.Transfer.TransportedRealCoordinates

namespace OAI

/-! The identified scalar is the ordinary smooth inverse transport on
the open limiting domain. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

theorem imageScalar_contDiffOn (hG : IsOpen d.physicalDomain) (i : Fin m) :
    ContDiffOn ℝ ∞ (R.imageScalar i)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) := by
  let f := extendAtInfinity R.limit.function
  let V := f '' d.physicalDomain
  have hV : IsOpen V := R.limit.conformal.1.isOpen_image hG hG (Subset.refl _)
  obtain ⟨fi, heq⟩ := R.limit.conformal.exists_smooth_inverse hG hV
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hfix : f OnePoint.infty = OnePoint.infty := rfl
  have htransport := (transported_real_coordinate heq hV hinf hfix
    (isOpen_realChartDomain hG) (Subset.refl _) (Q i).physical (Q i).physical_smooth).2.1
  have hc : ContDiffOn ℝ ∞ ((Q i).physical ∘ sphereRealMap fi ∘ Complex.equivRealProdCLM)
      (R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) := by
    apply htransport.comp Complex.equivRealProdCLM.contDiff.contDiffOn
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Complex.equivRealProdCLM x, ?_, ?_⟩
    · simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hx
    · simp only [sphereRealMap, extendAtInfinity_coe, finiteCoord_coe,
        ContinuousLinearEquiv.symm_apply_apply]
  apply hc.congr
  rintro _ ⟨x, hx, rfl⟩
  rw [R.imageScalar_apply hG i hx]
  symm
  change (Q i).physical (Complex.equivRealProdCLM
    (finiteCoord (fi (R.limit.function x)))) = (Q i).physical (Complex.equivRealProdCLM x)
  have he : fi (R.limit.function x) = (x : Sphere) := heq.left_inv x hx
  rw [he, finiteCoord_coe]

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
