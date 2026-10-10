import OAI.Analysis.CircleDomains.Probability.MeasurableArcIndex
import OAI.Analysis.CircleDomains.Topology.BoundaryStieltjes

namespace OAI

/-! The Borel arc index is averaged against the actual arc law. On the
boundary its average is the positive Stieltjes coordinate already proved. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def meanDiskArcIndex (η : ProbabilityMeasure C(PathTime, ℂ))
    (p : CircleLiftCover normalizedArgument) : ℝ :=
  ∫ γ, totalDiskArcIndex γ p ∂(η : Measure C(PathTime, ℂ))

theorem meanDiskArcIndex_translate (η : ProbabilityMeasure C(PathTime, ℂ))
    (p : CircleLiftCover normalizedArgument) (n : ℤ)
    (hi : Integrable (fun γ => totalDiskArcIndex γ p) (η : Measure C(PathTime, ℂ))) :
    meanDiskArcIndex η (p.translate n) = meanDiskArcIndex η p + (n : ℝ) := by
  simp only [meanDiskArcIndex, totalDiskArcIndex_translate,
    integral_add hi (integrable_const (n : ℝ)), integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]

def arcStartingAngleLaw (η : ProbabilityMeasure C(PathTime, ℂ)) : ProbabilityMeasure UnitAddCircle :=
  η.map (fun γ => normalizedArgument (γ 0))

theorem measurable_arcStartingAngle :
    Measurable (fun γ : C(PathTime, ℂ) => normalizedArgument (γ 0)) :=
  measurable_normalizedArgument.comp (continuous_eval_const 0).measurable

theorem totalDiskArcIndex_boundary_ae (η : ProbabilityMeasure C(PathTime, ℂ))
    (p : CircleLiftCover normalizedArgument) (hp : ‖p.base‖ = 1)
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)),
      ‖γ 0‖ = 1 ∧ γ 1 = 0 ∧ ∀ t, ‖γ t‖ ≤ 1)
    (hmiss : pathHitProbability η p.base = 0) :
    (fun γ => totalDiskArcIndex γ p) =ᵐ[(η : Measure C(PathTime, ℂ))]
      fun γ => (⌊p.height - unitCircleCut (normalizedArgument (γ 0))⌋ : ℝ) := by
  have hav : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), (γ, p.base) ∉ pathHitSet := by
    apply ae_iff.mpr
    simpa only [pathHitProbability, pathHitSet, mem_ofPred_eq, not_not] using hmiss
  filter_upwards [hη, hav] with γ hγ ha
  rw [totalDiskArcIndex_of_avoids γ p ha]
  exact diskArcIndex_boundary_floor ⟨(γ, p.base), ha⟩ p.height hγ.1 hp hγ.2.1 hγ.2.2 p.height_projects

theorem integrable_totalDiskArcIndex_boundary (η : ProbabilityMeasure C(PathTime, ℂ))
    (p : CircleLiftCover normalizedArgument) (hp : ‖p.base‖ = 1)
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)),
      ‖γ 0‖ = 1 ∧ γ 1 = 0 ∧ ∀ t, ‖γ t‖ ≤ 1)
    (hmiss : pathHitProbability η p.base = 0) :
    Integrable (fun γ => totalDiskArcIndex γ p) (η : Measure C(PathTime, ℂ)) := by
  apply Integrable.of_bound
    (measurable_totalDiskArcIndex.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (|p.height| + 2)
  filter_upwards [totalDiskArcIndex_boundary_ae η p hp hη hmiss] with γ hγ
  change ‖totalDiskArcIndex γ p‖ ≤ |p.height| + 2
  simpa only [hγ, Real.norm_eq_abs] using boundaryIndex_bound p.height (normalizedArgument (γ 0))

theorem meanDiskArcIndex_boundary (η : ProbabilityMeasure C(PathTime, ℂ))
    (p : CircleLiftCover normalizedArgument) (hp : ‖p.base‖ = 1)
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)),
      ‖γ 0‖ = 1 ∧ γ 1 = 0 ∧ ∀ t, ‖γ t‖ ≤ 1)
    (hmiss : pathHitProbability η p.base = 0) :
    meanDiskArcIndex η p = boundaryIndexMean (arcStartingAngleLaw η) p.height := by
  rw [meanDiskArcIndex, integral_congr_ae (totalDiskArcIndex_boundary_ae η p hp hη hmiss)]
  symm
  rw [boundaryIndexMean, arcStartingAngleLaw, ProbabilityMeasure.toMeasure_map,
    integral_map measurable_arcStartingAngle.aemeasurable
      (measurable_boundaryIndex p.height).aestronglyMeasurable]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
