import OAI.Analysis.CircleDomains.Topology.MeanArcIndex
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Dominated convergence for the explicit mean index. The local bound is
kept as a hypothesis here and must be supplied by the arc geometry. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

instance : FirstCountableTopology (CircleLiftCover normalizedArgument) :=
  (show Topology.IsInducing (fun p : CircleLiftCover normalizedArgument => p.val) from
    ⟨rfl⟩).firstCountableTopology

theorem continuousAt_meanDiskArcIndex
    (η : ProbabilityMeasure C(PathTime, ℂ)) (p : CircleLiftCover normalizedArgument)
    (hp : ‖p.base‖ < 1)
    (hstart : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), ‖γ 0‖ = 1)
    (hmiss : pathHitProbability η p.base = 0)
    (bound : C(PathTime, ℂ) → ℝ) (hb : Integrable bound (η : Measure C(PathTime, ℂ)))
    (hbound : ∀ᶠ q in 𝓝 p, ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)),
      ‖totalDiskArcIndex γ q‖ ≤ bound γ) :
    ContinuousAt (meanDiskArcIndex η) p := by
  have hav : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), (γ, p.base) ∉ pathHitSet := by
    apply ae_iff.mpr
    simpa only [pathHitProbability, pathHitSet, mem_ofPred_eq, not_not] using hmiss
  apply tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall fun q =>
      (measurable_totalDiskArcIndex.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    hbound hb
  filter_upwards [hstart, hav] with γ hγ ha
  exact continuousAt_totalDiskArcIndex γ hγ p hp ha

theorem integrable_totalDiskArcIndex_of_bound
    (η : ProbabilityMeasure C(PathTime, ℂ)) (p : CircleLiftCover normalizedArgument)
    (M : ℝ) (hM : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), |totalDiskArcIndex γ p| ≤ M) :
    Integrable (fun γ => totalDiskArcIndex γ p) (η : Measure C(PathTime, ℂ)) := by
  apply Integrable.of_bound
    (measurable_totalDiskArcIndex.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable M
  filter_upwards [hM] with γ hγ
  exact hγ

end CircleDomainRigidity.FiniteTransfer

end

end OAI
