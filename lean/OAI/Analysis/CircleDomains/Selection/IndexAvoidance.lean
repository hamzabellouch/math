import OAI.Analysis.CircleDomains.Selection.MeanIndexContinuity

namespace OAI

/-! An avoiding test path has constant sample index. Thus the mean index
also has equal endpoint values if almost every sample misses the test path. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem diskArcIndex_eq_along_avoiding_path (γ : C(PathTime, ℂ))
    (hstart : ‖γ 0‖ = 1) (hend : γ 1 = 0)
    (δ : C(PathTime, CircleLiftCover normalizedArgument))
    (hδ : ∀ t, ‖(δ t).base‖ < 1)
    (hmiss : ∀ t, (γ, (δ t).base) ∉ pathHitSet) :
    totalDiskArcIndex γ (δ 1) = totalDiskArcIndex γ (δ 0) := by
  let D : C(PathTime, DiskArcIndexDomain γ) :=
    ⟨fun t => ⟨δ t, hδ t, hmiss t⟩, δ.continuous.subtype_mk _⟩
  have hl := (isLocallyConstant_diskArcIndexValue γ hstart hend).comp_continuous D.continuous
  have he := hl.apply_eq_of_preconnectedSpace (1 : PathTime) 0
  simpa only [Function.comp_apply, D, ContinuousMap.coe_mk, diskArcIndexValue,
    totalDiskArcIndex_of_avoids γ (δ 1) (hmiss 1),
    totalDiskArcIndex_of_avoids γ (δ 0) (hmiss 0)] using he

theorem meanDiskArcIndex_eq_along_ae_avoiding_path
    (η : ProbabilityMeasure C(PathTime, ℂ))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), ‖γ 0‖ = 1 ∧ γ 1 = 0)
    (δ : C(PathTime, CircleLiftCover normalizedArgument))
    (hδ : ∀ t, ‖(δ t).base‖ < 1)
    (hmiss : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)),
      ∀ t, (γ, (δ t).base) ∉ pathHitSet) :
    meanDiskArcIndex η (δ 1) = meanDiskArcIndex η (δ 0) := by
  apply integral_congr_ae
  filter_upwards [hη, hmiss] with γ hγ hm
  exact diskArcIndex_eq_along_avoiding_path γ hγ.1 hγ.2 δ hδ hm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
