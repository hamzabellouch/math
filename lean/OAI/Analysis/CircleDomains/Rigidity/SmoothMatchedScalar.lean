import OAI.Analysis.CircleDomains.Sobolev.SmoothPullbackFiniteEnergy
import OAI.Analysis.CircleDomains.Topology.ProjectedPlaneFunction
import OAI.Analysis.CircleDomains.Selection.PointDustContourSelection
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! A compact smooth target scalar supplies all analytic hypotheses of
the actual matched mask. In particular its source differential is L². -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer MatchedConformalEnds
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem smooth_compact_sphere_scalar {Φ : EuclideanPlane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    Continuous (sphereFromPlaneFunction Φ) ∧
      (∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), sphereFromPlaneFunction Φ p = 0) ∧
      ∃ L : ℝ≥0, LipschitzWith L (fun z : ℂ => sphereFromPlaneFunction Φ (z : Sphere)) := by
  refine ⟨continuous_sphereFromPlaneFunction hΦ.continuous hs,
    sphereFromPlaneFunction_zero_near_infty hs,?_⟩
  let g := Φ ∘ complexPlaneCoordinates.symm
  have hg : ContDiff ℝ ∞ g := hΦ.comp complexPlaneCoordinates.symm.contDiff
  have hgs : HasCompactSupport g := hs.comp_homeomorph complexPlaneCoordinates.symm.toHomeomorph
  obtain ⟨B,hB⟩ := (hg.continuous_fderiv (by simp)).bounded_above_of_compact_support (hgs.fderiv ℝ)
  let L : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hl : LipschitzWith L g := lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) (by
    intro z
    change ‖fderiv ℝ g z‖ ≤ max B 0
    exact (hB z).trans (le_max_left _ _))
  have he : (fun z : ℂ => sphereFromPlaneFunction Φ (z : Sphere)) = g :=
    funext (fun z => sphereFromPlaneFunction_coe Φ z)
  rw [he]
  exact ⟨L,hl⟩

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem smooth_selected_scalar_finite_energy
    (hG : IsOpen G) (hH : IsOpen (f '' G)) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    ContDiffOn ℝ 1 (D.realSelectedScalar hG hf (sphereFromPlaneFunction Φ)) (realPlaneDomain G) ∧
      MemLp (fderiv ℝ (D.realSelectedScalar hG hf (sphereFromPlaneFunction Φ))) 2
        (volume.restrict (realPlaneDomain G)) := by
  have hfull := hf
  obtain ⟨hfc,hmap,fi,hfic,himap,hl,hr⟩ := hf
  let heq : IsSmoothSphereEquivalence f fi G (f '' G) :=
    ⟨fun p hp => hfc.isSmoothSphereAt hG hp,hmap,
      fun p hp => hfic.isSmoothSphereAt hH hp,himap,hl,hr⟩
  obtain ⟨hb,hb2⟩ := smooth_pullback_finite_energy heq hG hH hinf hfix hfic hΦ hs
  have he : EqOn (D.realSelectedScalar hG hfull (sphereFromPlaneFunction Φ))
      (Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f) (realPlaneDomain G) := by
    intro p hp
    rw [realSelectedScalar,D.selectedTarget_on_domain hG hfull hp]
    have hfin := heq.finite_forward hinf hfix hp
    simp only [sphereFromPlaneFunction,ite_eq_right hfin,comp_apply,sphereRealMap]
    rfl
  refine ⟨hb.congr (fun p hp => he hp),?_⟩
  apply hb2.ae_eq
  filter_upwards [ae_restrict_mem (realPlaneDomain_open hG).measurableSet] with p hp
  exact (he.eventuallyEq_of_mem ((realPlaneDomain_open hG).mem_nhds hp)).fderiv_eq.symm

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
