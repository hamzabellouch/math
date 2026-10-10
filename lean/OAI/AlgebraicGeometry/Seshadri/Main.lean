import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.ProjectiveCartier
import OAI.AlgebraicGeometry.Seshadri.Intersection.FiniteLineEuler
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalDivisorDegree
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalIdealEuler
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticDivision
import OAI.AlgebraicGeometry.Seshadri.Intersection.CurveSectionDegree
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ClosedPushforwardExact
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CycleStructures
import OAI.AlgebraicGeometry.Seshadri.Intersection.ArbitraryCartierEuler
import OAI.AlgebraicGeometry.Seshadri.Sheaves.BaseChangeNatural
import OAI.AlgebraicGeometry.Seshadri.Interpolation.SurfaceQuadrilateral
import OAI.AlgebraicGeometry.Seshadri.Geometry.AmplePowers
import OAI.AlgebraicGeometry.Seshadri.Blowup.BoundaryNef
import OAI.AlgebraicGeometry.Seshadri.Interpolation.SeshadriUpper

namespace OAI


                                  
section

namespace MaximalSeshadri.Geometry

theorem maximalSeshadriConstants (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) : EventualMaximalSeshadri S L := by
  obtain ⟨r₀,hr₀,h⟩ := S.eventual_very_general_curve_lower L hL
  refine ⟨r₀,hr₀,fun r hr => ?_⟩
  obtain ⟨Z,hZ,hne,hC⟩ := h r hr
  refine ⟨Z,hZ,hne,fun p hp => ?_⟩
  have hrpos : 0 < r := hr₀.trans_le hr
  obtain ⟨B⟩ := S.pointBlowup_exists L hL r p
  exact ⟨⟨B,B.boundaryNef_of_curve_bound S L hL hrpos (hC p hp)⟩,
    S.seshadri_eq_of_curve_lower L hL hrpos p (hC p hp)⟩

end MaximalSeshadri.Geometry

end



end OAI
