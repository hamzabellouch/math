import OAI.Analysis.CircleDomains.Rigidity.FiniteMatchedField
import OAI.Analysis.CircleDomains.Rigidity.AxialLineDifferentiation
import OAI.Analysis.CircleDomains.Rigidity.SmoothMatchedScalar

namespace OAI

/-! Smoothness on the domain of the actual finite chart and of a compact
smooth scalar pulled back along either source axis. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)
include D

 theorem finite_part_contDiffOn (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    ContDiffOn ℝ ∞ (fun z : ℂ => finiteCoord (f (z : Sphere))) {z | (z : Sphere) ∈ G} := by
  apply DifferentiableOn.contDiffOn _ (hG.preimage OnePoint.continuous_coe) |>.restrict_scalars ℝ
  intro z hz
  exact (analyticAt_finite_map_of_conformal hG hf.1 hz
    (D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hz))).differentiableAt.differentiableWithinAt

 theorem sphere_scalar_line_contDiffOn
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin 2) (y : ℝ) :
    ContDiffOn ℝ 1 (fun x => sphereFromPlaneFunction Φ (f (complexCoordinateLine i y x : Sphere)))
      {x | (complexCoordinateLine i y x : Sphere) ∈ G} := by
  have hF := D.finite_part_contDiffOn hG hinf hf hfix
  have hb := hΦ.comp_contDiffOn (complexPlaneCoordinates.symm.contDiff.comp_contDiffOn hF)
  have hl := hb.comp (complexCoordinateLine_contDiff i y).contDiffOn
    (show MapsTo (complexCoordinateLine i y) {x | (complexCoordinateLine i y x : Sphere) ∈ G}
      {z | (z : Sphere) ∈ G} from fun _ hx => hx)
  apply (hl.of_le (by simp)).congr
  intro x hx
  have hne := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hx)
  simp only [sphereFromPlaneFunction,ite_eq_right hne,Function.comp_apply]

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
