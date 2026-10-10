import OAI.Geometry.SurfaceImmersion.Geometry.MetricGaussInvariance
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCoordinateData

namespace OAI

/-! An actual orthonormal normal frame and the Gauss-constrained coordinates
of the second fundamental form of a smooth surface in four-space. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

structure SecondFormFrame (F : RField 4) (p : Base) (k : ℝ) where
  n : Vec
  m : Vec
  S : ℝ
  D : ℝ
  N : ℝ
  L : ℝ
  size_pos : 0 < S
  unit_n : n ⬝ᵥ n = 1
  unit_m : m ⬝ᵥ m = 1
  orthogonal : n ⬝ᵥ m = 0
  tangent_n : coordDeriv dx F p ⬝ᵥ n = 0 ∧ coordDeriv dy F p ⬝ᵥ n = 0
  tangent_m : coordDeriv dx F p ⬝ᵥ m = 0 ∧ coordDeriv dy F p ⬝ᵥ m = 0
  xx : realSecondForm F dx dx p = ((k+D^2+N^2)/S) • n+L • m
  xy : realSecondForm F dx dy p = D • n+N • m
  yy : realSecondForm F dy dy p = S • n

theorem exists_secondFormFrame_with_coordinates {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : realSecondForm F dy dy p ≠ 0) :
    ∃ d : SecondFormFrame F p
      (coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p),
      d.n = normalize (realSecondForm F dy dy p) ∧
      d.m = unitPerp (coordDeriv dx F p) (coordDeriv dy F p) d.n ∧
      d.S = Real.sqrt (realSecondForm F dy dy p ⬝ᵥ realSecondForm F dy dy p) ∧
      d.D = realSecondForm F dx dy p ⬝ᵥ d.n ∧
      d.N = realSecondForm F dx dy p ⬝ᵥ d.m ∧
      d.L = realSecondForm F dx dx p ⬝ᵥ d.m := by
  let X := coordDeriv dx F p
  let Y := coordDeriv dy F p
  let B := realSecondForm F dy dy p
  let n := normalize B
  let m := unitPerp X Y n
  let S := Real.sqrt (B ⬝ᵥ B)
  let Bxx := realSecondForm F dx dx p
  let Bxy := realSecondForm F dx dy p
  let D := Bxy ⬝ᵥ n
  let N := Bxy ⬝ᵥ m
  let L := Bxx ⬝ᵥ m
  let k := coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p
  have hperp (v w : Base) : X ⬝ᵥ realSecondForm F v w p = 0 ∧
      Y ⬝ᵥ realSecondForm F v w p = 0 := realNormalPart_perp X Y _ hD
  have hn : n ⬝ᵥ n = 1 := normalize_unit hB
  have hnn : n ≠ 0 := normalize_nonzero hB
  have hXn : X ⬝ᵥ n = 0 := dot_normalize_zero (hperp dy dy).1
  have hYn : Y ⬝ᵥ n = 0 := dot_normalize_zero (hperp dy dy).2
  obtain ⟨hXm,hYm,hnm⟩ := unitPerp_orthogonal X Y n
  have hm : m ⬝ᵥ m = 1 := unitPerp_unit hD hnn hXn hYn
  have hS : 0 < S := Real.sqrt_pos.mpr (VelocityFrame.dot_self_pos hB)
  have hyy : B = S • n := (norm_smul_normalize hB).symm
  have hreconstruct (v w : Base) : realSecondForm F v w p =
      (realSecondForm F v w p ⬝ᵥ n) • n+(realSecondForm F v w p ⬝ᵥ m) • m := by
    have hr := plane_coordinates_reconstruct hD hn hm hnm hXn hXm hYn hYm
      (hperp v w).1 (hperp v w).2
    simpa only [planeLift_apply,VelocityFrame.planeCoordinates,Matrix.cons_val_zero,
      Matrix.cons_val_one] using hr.symm
  have hlength : D^2+N^2 = Bxy ⬝ᵥ Bxy :=
    plane_coordinates_length hD hn hm hnm hXn hXm hYn hYm (hperp dx dy).1 (hperp dx dy).2
  have hgauss : Bxx ⬝ᵥ B-Bxy ⬝ᵥ Bxy = k := gauss_metric_identity hF p hD
  rw [hyy,dotProduct_smul] at hgauss
  change S*(Bxx ⬝ᵥ n)-Bxy ⬝ᵥ Bxy = k at hgauss
  have hcoef : Bxx ⬝ᵥ n = (k+D^2+N^2)/S := by
    apply (eq_div_iff hS.ne').mpr
    nlinarith
  refine ⟨{
    n := n
    m := m
    S := S
    D := D
    N := N
    L := L
    size_pos := hS
    unit_n := hn
    unit_m := hm
    orthogonal := hnm
    tangent_n := ⟨hXn,hYn⟩
    tangent_m := ⟨hXm,hYm⟩
    xx := ?_
    xy := hreconstruct dx dy
    yy := hyy },rfl,rfl,rfl,rfl,rfl,rfl⟩
  rw [hreconstruct dx dx]
  change (Bxx ⬝ᵥ n) • n+L • m = _
  rw [hcoef]


theorem exists_secondFormFrame {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : realSecondForm F dy dy p ≠ 0) :
    Nonempty (SecondFormFrame F p
      (coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p)) := by
  obtain ⟨d,_⟩ := exists_secondFormFrame_with_coordinates hF p hD hB
  exact ⟨d⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
