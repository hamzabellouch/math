import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelAngularMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularAdditiveMellin
import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinAngularFunctional

namespace OAI

/-! Entire completed additive angular Dirichlet series and their paired Mellin identity. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaLevelAngularCompleted_functional {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    cubicThetaLevelAngularCompleted q x y rev k s=
      cubicThetaLevelAngularPhase q x rev k*
        mellin (cubicThetaScaledAngularAxis (cubicThetaCircleOrder (!rev) k)
          (3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale q)) (((2*k:ℕ):ℂ)-s) := by
  rw [←(cubicThetaLevelAngular_mellin hq x y hxy rev hk s).2]
  exact theta_mellin_functional_angular k
    (fun t ht => cubicThetaLevelAngularAxis_functional hq x y hxy rev hk ht) s

theorem cubicThetaLevelAngular_actual_entire {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k) :
    Differentiable ℂ (mellin (cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
      (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q))) := by
  have he : mellin (cubicThetaScaledAngularAxis (cubicThetaCircleOrder rev k)
      (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaLevelScale q))=
        cubicThetaLevelAngularCompleted q x y rev k := by
    funext s
    exact (cubicThetaLevelAngular_mellin hq x y hxy rev hk s).2
  rw [he]
  exact cubicThetaLevelAngularCompleted_entire hq x y rev k

theorem cubicThetaLevelAngularCompleted_dirichlet {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaLevelAngularCompleted q x y rev k (2*s+(k:ℂ)-1)=
      (cubicThetaLevelScale q:ℂ)^(-(2*s+(k:ℂ)-1))*
        ((1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(k:ℂ)/2))*
          Complex.Gamma (s+(k:ℂ)/2+1/6)*Complex.Gamma (s+(k:ℂ)/2-1/6)*
          cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder rev k) n*
            cubicThetaAdditiveCoefficient (-(3*(x:ℂ)/(q:ℂ))) n) (2*s-1)) := by
  rw [←(cubicThetaLevelAngular_mellin hq x y hxy rev hk _).2]
  change mellin (fun t : ℝ => cubicThetaNonconstant
    (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder rev k))
      (-(3*(x:ℂ)/(q:ℂ)),cubicThetaLevelScale q*t)) (2*s+(k:ℂ)-1)=_
  rw [mellin_comp_mul_left (fun v : ℝ => cubicThetaNonconstant
    (cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient (cubicThetaCircleOrder rev k))
      (-(3*(x:ℂ)/(q:ℂ)),v)) _ (cubicThetaLevelScale_pos hq)]
  have horder : (cubicThetaCircleOrder rev k).natAbs=k := by
    cases rev <;> simp [cubicThetaCircleOrder]
  have H := cubicThetaAngularAdditive_mellin (-(3*(x:ℂ)/(q:ℂ))) (cubicThetaCircleOrder rev k) hs
  rw [horder] at H
  rw [H]
  rfl

end CubicFirstMoment

end

end OAI
