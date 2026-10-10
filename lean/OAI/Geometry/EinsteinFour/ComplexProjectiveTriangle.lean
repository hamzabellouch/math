import OAI.Geometry.EinsteinFour.ComplexPairAlignment
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

namespace OAI

/-! The triangle inequality for the actual Fubini--Study distance on CP2. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complex_unit_angle (u v : CP2Vector) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    InnerProductGeometry.angle u v = Real.arccos (inner ℝ u v) := by
  simp only [InnerProductGeometry.angle,hu,hv,one_mul,div_one]

theorem fubiniStudyDistance_triangle (P Q R : ComplexProjective2) :
    fubiniStudyDistance P R ≤ fubiniStudyDistance P Q + fubiniStudyDistance Q R := by
  obtain ⟨p,hp,hpn,hpP,hqp⟩ := cp2_aligned_unit_representative Q P
  obtain ⟨r,hr,hrn,hrR,hqr⟩ := cp2_aligned_unit_representative Q R
  let q := cp2UnitRep Q
  have hpqR : inner ℝ q p = cp2Overlap Q P := by
    simpa only [Complex.ofReal_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hqp
  have hqrR : inner ℝ q r = cp2Overlap Q R := by
    simpa only [Complex.ofReal_re,← real_inner_eq_re_inner ℂ] using! congrArg Complex.re hqr
  have hreal : inner ℝ p r ≤ ‖inner ℂ p r‖ := by
    simpa only [← real_inner_eq_re_inner ℂ] using! Complex.re_le_norm (inner ℂ p r)
  calc
    fubiniStudyDistance P R = Real.arccos ‖inner ℂ p r‖ := by
      rw [fubiniStudyDistance_eq_arccos,cp2Overlap_of_unit_representatives P R p r hp hr hpn hrn hpP hrR]
    _ ≤ InnerProductGeometry.angle p r := by
      rw [complex_unit_angle p r hpn hrn]
      exact Real.antitone_arccos hreal
    _ ≤ InnerProductGeometry.angle p q + InnerProductGeometry.angle q r :=
      InnerProductGeometry.angle_le_angle_add_angle p q r
    _ = fubiniStudyDistance P Q + fubiniStudyDistance Q R := by
      rw [complex_unit_angle p q hpn (cp2UnitRep_norm Q),
        complex_unit_angle q r (cp2UnitRep_norm Q) hrn,
        real_inner_comm q p,hpqR,hqrR,cp2Overlap_comm Q P,
        fubiniStudyDistance_eq_arccos,fubiniStudyDistance_eq_arccos]

end
end PositiveEinsteinFour.Geometry

end OAI
