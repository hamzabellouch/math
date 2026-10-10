import OAI.Geometry.CylinderCovering.Angular.CubicTheoremDefinitions
import OAI.Geometry.CylinderCovering.Angular.CubicFamily
import OAI.Geometry.CylinderCovering.Angular.CubicCost
import OAI.Geometry.CylinderCovering.Cubic.Similarity

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic
open TriangularCovering

lemma minimumShadow4_eq : minimumShadow4 = 4 * H := K4_projection_minimum

theorem fullCubic_proof : FullCubicStatement := by
  refine ⟨minimumShadow4_eq, finiteCover_proof, ?_, cubicCost_bigO,
    (1 / 100000 : ℝ), by norm_num, ?_⟩
  · intro eps he0 he1
    exact cubicCost_expansion he0 he1
  · intro eps he0 he1
    obtain ⟨C, hcover, harea, hprescribed⟩ := finiteCover_proof eps he0 (by linarith)
    refine ⟨C, hcover, hprescribed, harea, ?_⟩
    rw [harea, minimumShadow4_eq]
    have h := cubicCost_strict he0 he1.le
    linarith

end CylinderCovering.Cubic

end

end OAI
