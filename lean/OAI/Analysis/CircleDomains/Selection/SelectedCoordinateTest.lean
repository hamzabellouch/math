import OAI.Analysis.CircleDomains.Topology.CompactCoordinateTest
import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskData

namespace OAI

/-! A compact scalar test recovers each actual finite target coordinate
on all source complementary components. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem selectedTarget_outside (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    D.selectedTarget hG hf q ∈ (f '' G)ᶜ := by
  obtain ⟨p,_,he⟩ := D.componentRelation_source_fiber hG hf hq
  have hm : D.selectedTarget hG hf q ∈ {p' | D.componentRelation q p'} :=
    D.selectedTarget_mem hG hf q
  rw [he] at hm
  exact connectedComponentIn_subset _ _ hm

 theorem exists_smooth_selected_coordinate_test
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsOpen (f '' G)) (hinf' : OnePoint.infty ∈ f '' G) (k : Fin 2) :
    ∃ Φ : EuclideanPlane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      ∀ z : ℂ, (z : Sphere) ∈ Gᶜ →
        D.realSelectedScalar hG hf (sphereFromPlaneFunction Φ) (Complex.equivRealProdCLM z) =
          (complexPlaneCoordinates.symm (finiteCoord (D.selectedTarget hG hf (z : Sphere)))) k := by
  obtain ⟨Φ,hΦ,hs,hcoord⟩ := exists_smooth_compact_coordinate_test hH hinf' k
  refine ⟨Φ,hΦ,hs,?_⟩
  intro z hz
  have hp := D.selectedTarget_outside hG hf hz
  unfold realSelectedScalar
  rw [ContinuousLinearEquiv.symm_apply_apply]
  generalize hq : D.selectedTarget hG hf (z : Sphere) = q at hp ⊢
  cases q using OnePoint.rec with
  | infty => exact (hp hinf').elim
  | coe w => simpa only [finiteCoord_coe] using hcoord w hp

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
