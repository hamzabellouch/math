import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridAnalytic

namespace OAI

/-! Coordinate lines used for the spatial derivatives of the series. -/
noncomputable section
namespace CubicFirstMoment

inductive CubicThetaAxis where
  | x | y | height

def cubicThetaCoordinateLine (k : CubicThetaAxis) (x y v t : ℝ) : ℂ × ℝ :=
  match k with
  | .x => cubicThetaCartesianPoint t y v
  | .y => cubicThetaCartesianPoint x t v
  | .height => cubicThetaCartesianPoint x y t

def cubicThetaCoordinateCenter (k : CubicThetaAxis) (x y v : ℝ) : ℝ :=
  match k with
  | .x => x
  | .y => y
  | .height => v

lemma cubicThetaCoordinateLine_center (k : CubicThetaAxis) (x y v : ℝ) :
    cubicThetaCoordinateLine k x y v (cubicThetaCoordinateCenter k x y v)=
      cubicThetaCartesianPoint x y v := by
  cases k <;> rfl

lemma cubicThetaCoordinateLine_continuous (k : CubicThetaAxis) (x y v : ℝ) :
    Continuous (cubicThetaCoordinateLine k x y v) := by
  cases k <;> unfold cubicThetaCoordinateLine cubicThetaCartesianPoint <;> fun_prop

lemma cubicThetaCoordinateLine_analytic (k : CubicThetaAxis) (cd : Eisenstein × Eisenstein)
    (s : ℂ) (x y v t : ℝ) (ht : 0<(cubicThetaCoordinateLine k x y v t).2) :
    AnalyticAt ℝ (fun w : ℝ => cubicThetaEisensteinGridTerm cd
      (cubicThetaCoordinateLine k x y v w) s) t := by
  cases k with
  | x => exact (cubicThetaEisensteinGrid_analytic cd.1 cd.2 s t y ht).1
  | y => exact (cubicThetaEisensteinGrid_analytic cd.1 cd.2 s x t ht).2.1
  | height => exact (cubicThetaEisensteinGrid_analytic cd.1 cd.2 s x y ht).2.2

end CubicFirstMoment

end

end OAI
