import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularFunctionalEquation
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticVoronoi

namespace OAI

/-! The actual angular functional equation has the Gamma quotient occurring
in the published Voronoi transform. No Voronoi identity is used here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngular_archimedean_ratio {q : Eisenstein} (hq : primary q)
    (rev : Bool) (k : ℕ) (s : ℂ) :
    cubicThetaAngularUncompletion q k s*cubicThetaAngularCompletion q k (1-s)=
      (cubicThetaLevelScale q:ℂ)^(4*s-2)*((2*Real.pi:ℝ):ℂ)^(4*s-2)*
        metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s := by
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hkabs : ((|cubicThetaCircleOrder rev k|:ℤ):ℂ)=(k:ℂ) := by
    cases rev <;> simp [cubicThetaCircleOrder]
  have hρp : (cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*
      (cubicThetaLevelScale q:ℂ)^(-(2*(1-s)+(k:ℂ)-1))=
        (cubicThetaLevelScale q:ℂ)^(4*s-2) := by
    rw [←Complex.cpow_add _ _ hρ]
    congr 1
    ring
  have hπp : ((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*
      ((2*Real.pi:ℝ):ℂ)^(-(2*(1-s)+(k:ℂ)))=((2*Real.pi:ℝ):ℂ)^(4*s-2) := by
    rw [←Complex.cpow_add _ _ hπ]
    congr 1
    ring
  have hplus : 1-s+(k:ℂ)/2+1/6=7/6+(k:ℂ)/2-s := by ring
  have hminus : 1-s+(k:ℂ)/2-1/6=5/6+(k:ℂ)/2-s := by ring
  unfold cubicThetaAngularUncompletion cubicThetaAngularCompletion
  rw [hplus,hminus]
  calc
    _ = ((cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*
          (cubicThetaLevelScale q:ℂ)^(-(2*(1-s)+(k:ℂ)-1)))*
        (((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*((2*Real.pi:ℝ):ℂ)^(-(2*(1-s)+(k:ℂ))))*
          metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s := by
      simp only [metaplecticGammaQuotient,hkabs,div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [hρp,hπp]

theorem cubicThetaAngularDirichletContinuation_gamma_functional {q : Eisenstein}
    (hq : primary q) (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool)
    {k : ℕ} (hk : 0<k) {s : ℂ} (hs : s.re<5/6+(k:ℝ)/2) :
    cubicThetaAngularDirichletContinuation q x y rev k s=
      cubicThetaLevelAngularPhase q x rev k*
        (cubicThetaLevelScale q:ℂ)^(4*s-2)*((2*Real.pi:ℝ):ℂ)^(4*s-2)*
          metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s*
            cubicThetaAngularDirichletContinuation q (-y) (-x) (!rev) k (1-s) := by
  rw [cubicThetaAngularDirichletContinuation_functional hq x y hxy rev hk hs]
  calc
    _ = cubicThetaLevelAngularPhase q x rev k*
        (cubicThetaAngularUncompletion q k s*cubicThetaAngularCompletion q k (1-s))*
          cubicThetaAngularDirichletContinuation q (-y) (-x) (!rev) k (1-s) := by ring
    _ = _ := by rw [cubicThetaAngular_archimedean_ratio hq rev k s]; ring

end CubicFirstMoment

end

end OAI
