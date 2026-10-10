import OAI.Geometry.NodalSets.Elliptic.RealMatrixEnergyProducts

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

def realTransportQuadratic (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (x xi : Yau.Jets.Coord) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    (2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i*xi k*xi j -
      V x k*Yau.coordPartial (fun y ↦ B y i j) x k*xi i*xi j)

lemma realTransportDeformation_eq_quadratic (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realTransportDeformation B V v x = realTransportQuadratic B V x (realCoordGradient v x) := rfl

def realGradientSquare (v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  ∑ i, (Yau.coordPartial v x i)^2

lemma realGradientSquare_smooth (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (realGradientSquare v) :=
  ContDiff.sum (fun i _ ↦ (Yau.real_coordPartial_smooth v hv i).pow 2)

lemma realGradientSquare_compact (v : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport v) :
    HasCompactSupport (realGradientSquare v) := by
  have hd (i : Fin 4) : HasCompactSupport (fun x ↦ (Yau.coordPartial v x i)^2) := by
    convert (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right
      (f' := fun x ↦ Yau.coordPartial v x i) using 1
    first | rfl | (ext x; simp [pow_two,Yau.coordPartial])
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦ hd i)
  exact h

lemma realCoordGradient_zero_off_support (v : Yau.Jets.Coord → ℝ)
    {x : Yau.Jets.Coord} (hx : x ∉ tsupport v) : realCoordGradient v x = 0 := by
  ext i
  simp only [realCoordGradient,Yau.coordPartial,fderiv_of_notMem_tsupport ℝ hx,
    _root_.zero_apply,Pi.zero_apply]

end
end Yau.Geometry

end OAI
