import OAI.Geometry.CylinderCovering.Cartesian.CoverEligibility
import OAI.Geometry.CylinderCovering.Angular.GeneralTheorem

namespace OAI

open Set
namespace CylinderCovering.CartesianCaps

theorem cartesian_cover : CartesianCoverStatement := by
  intro η hη hη480 M hM
  obtain ⟨δ, A, hδ, hA, hg⟩ :=
    AngularGeneral.general_cap η hη hη480 (max M 12) (le_max_of_le_right (by norm_num))
  refine ⟨min δ (1/4), A, lt_min hδ (by norm_num), hA, ?_⟩
  intro τ hτ hτδ N a hN ha0 haN ha hmesh
  have ht : τ ∈ Icc (0 : ℝ) (1/4) :=
    ⟨hτ.le, (hτδ.trans_le (min_le_right _ _)).le⟩
  have he : η ∈ Ioc (0 : ℝ) 1 := ⟨hη, by linarith⟩
  have hd := cartesianData_admissible hN ha0 haN ha ht he hM hmesh
  refine ⟨hg τ hτ (hτδ.trans_le (min_le_left _ _)) _ hd, ?_⟩
  intro b hb j hj
  have hraw := AngularOrdinaryCaps.ordinaryData_admissible .radial
    hN ha0 haN ha hη.le hM hmesh
  have hn := hraw.2.2.2.2.1
  constructor
  · exact cartesian_lowerIntercept τ η b
      (AngularOrdinaryCaps.ordinaryData .radial N a τ η) ht he hb hn j hj
  · exact cartesian_upperIntercept τ η b
      (AngularOrdinaryCaps.ordinaryData .radial N a τ η) ht he hb hn j hj

end CylinderCovering.CartesianCaps

end OAI
