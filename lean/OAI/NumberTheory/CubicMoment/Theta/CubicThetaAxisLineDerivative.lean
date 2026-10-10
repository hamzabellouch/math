import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAxisDifferentials

namespace OAI

/-! Pure coordinate second derivatives are derivatives along the
corresponding fixed real tangent direction. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAxisFirst_translate (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    (p : ℂ × ℝ) (t : ℝ) :
    cubicThetaAxisFirst k f (p+t • cubicThetaAxisVector k)=
      deriv (fun w => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 w))
        (cubicThetaCoordinateCenter k p.1.re p.1.im p.2+t) := by
  cases k <;> simp [cubicThetaAxisFirst,cubicThetaAxisVector,cubicThetaCoordinateCenter,
    cubicThetaCoordinateLine,cubicThetaCartesianPoint,Complex.real_smul]

lemma cubicThetaAxisFirst_hasLineDerivAt (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    (p : ℂ × ℝ)
    (hf : ContDiffAt ℝ 2 (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    HasLineDerivAt ℝ (cubicThetaAxisFirst k f) (cubicThetaAxisSecond k f p) p (cubicThetaAxisVector k) := by
  have hd := ((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hi := (hasDerivAt_id (0:ℝ)).const_add (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)
  have h := hd.scomp_of_eq 0 hi (by simp)
  change HasDerivAt (fun t => cubicThetaAxisFirst k f (p+t • cubicThetaAxisVector k))
    (cubicThetaAxisSecond k f p) 0
  simpa only [cubicThetaAxisFirst_translate,one_smul,cubicThetaAxisSecond,Function.comp_def,id_eq] using h

end CubicFirstMoment

end

end OAI
