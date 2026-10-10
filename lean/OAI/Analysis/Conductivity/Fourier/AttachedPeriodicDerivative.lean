import Mathlib
import OAI.Analysis.Conductivity.Sobolev.FiniteEndPhysicalH1

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_covector {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (a b : ℝ) (x : Coord3) :
    (fun k => direction (Pi.single k 1) (fun y => f (flatEndCoordinates a b y)) x)=
      endAxialMatrix a*ᵥ(fun k => fderiv ℝ f (flatEndCoordinates a b x) (Pi.single k 1)) := by
  have he := (hf (flatEndCoordinates a b x)).hasFDerivAt.comp x (endAxialAffine_hasFDeriv a b x)
  ext k
  change fderiv ℝ (f ∘ flatEndCoordinates a b) x (Pi.single k 1)=_
  rw [he.fderiv]
  change fderiv ℝ f (flatEndCoordinates a b x) (endAxialMatrix a*ᵥPi.single k 1)=_
  simp only [endAxialMatrix, Matrix.diagonal_mulVec_single, Matrix.mulVec_diagonal]
  rw [show Pi.single k (![a,1,1] k * (1:ℝ)) =
      ![a,1,1] k • (Pi.single k (1:ℝ) : Coord3) by
    ext j
    by_cases hj : j=k
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]]
  rw [map_smul]
  rfl

lemma attachedPeriodicField_fderiv {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (a b : ℝ) (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) (v : Coord3) :
    fderiv ℝ (attachedPeriodicField f a b) (sourceCollarPiece i j x) v=
      (attachedCartesianMatrix a i j x*ᵥ(fun k => fderiv ℝ f
        (flatEndCoordinates a b (sourceFaceAngles i j x)) (Pi.single k 1))) ⬝ᵥ v := by
  rw [attachedPeriodicField,physicalPeriodicField_fderiv (hp.flatEnd a b)
    (hf.comp ((contDiff_flatEndCoordinates a b).differentiable (by norm_num))) i j hx v,
    flatEndCoordinates_covector hf,attachedCartesianMatrix,Matrix.mulVec_mulVec]

lemma attachedPeriodicField_covector {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (a b : ℝ) (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    (fun k => lineDeriv ℝ (attachedPeriodicField f a b) (sourceCollarPiece i j x) (Pi.single k 1))=
      attachedCartesianMatrix a i j x*ᵥ(fun k => fderiv ℝ f
        (flatEndCoordinates a b (sourceFaceAngles i j x)) (Pi.single k 1)) := by
  have hd := (physicalPeriodicField_hasFDeriv (hp.flatEnd a b)
    (hf.comp ((contDiff_flatEndCoordinates a b).differentiable (by norm_num))) i j hx).differentiableAt
  change DifferentiableAt ℝ (attachedPeriodicField f a b) (sourceCollarPiece i j x) at hd
  ext k
  rw [hd.lineDeriv_eq_fderiv,attachedPeriodicField_fderiv hp hf a b i j hx]
  simp

end ScalarConductivity

end
end

end OAI
