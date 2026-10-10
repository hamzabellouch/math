import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDirichletBounds
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularGammaEquation
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticGammaRecurrence

namespace OAI

/-! Polynomial bounds on far-left lines for the actual continued angular series. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaAngularDirichletContinuation_left_bound {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k)
    {m : ℕ} (hm : 2 ≤ m) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = 1/2 - (m:ℝ) →
      ‖cubicThetaAngularDirichletContinuation q x y rev k s‖≤C*(1+|s.im|)^(4*m) := by
  obtain ⟨G,hG,hΓ⟩ := metaplecticGamma_half_integer_bound (cubicThetaCircleOrder rev k) m
  let A := cubicThetaLevelScale q^(-4*(m:ℝ))*(2*Real.pi)^(-4*(m:ℝ))
  let B := 81*cubicThetaDirichletNormMass (2*(m:ℝ))
  let ε := cubicThetaLevelAngularPhase q x rev k
  have hA : 0≤A := mul_nonneg (Real.rpow_nonneg (cubicThetaLevelScale_pos hq).le _)
    (Real.rpow_nonneg (by positivity) _)
  have hB : 0≤B := mul_nonneg (by norm_num) (cubicThetaDirichletNormMass_nonneg _)
  refine ⟨‖ε‖*A*G*B,by positivity,?_⟩
  intro s hs
  have hmR : (2:ℝ)≤ m := by exact_mod_cast hm
  have he : s=(1/2:ℂ)-(m:ℂ)+(s.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [hs]
  have hgamma : ‖metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s‖≤G*(1+|s.im|)^(4*m) := by
    rw [he]
    simpa using hΓ s.im
  have hpair : q∣9*(-y)*(-x)-1 := by convert hxy using 1; ring
  have hdual := cubicThetaAngularDirichletContinuation_right_bound hq (-y) (-x) hpair (!rev) hk
    (σ := 1/2+(m:ℝ)) (by linarith) (1-s) (by simp [hs]; ring)
  have hb : ‖cubicThetaAngularDirichletContinuation q (-y) (-x) (!rev) k (1-s)‖≤B := by
    simpa only [show 2*(1/2+(m:ℝ))-1=2*(m:ℝ) by ring] using hdual
  have hpow : (4*s-2).re= -4*(m:ℝ) := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,hs]
    ring
  have hfac : ‖(cubicThetaLevelScale q:ℂ)^(4*s-2)‖*‖((2*Real.pi:ℝ):ℂ)^(4*s-2)‖=A := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (cubicThetaLevelScale_pos hq),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<2*Real.pi),hpow]
  have hs' : s.re<5/6+(k:ℝ)/2 := by
    have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
    linarith
  rw [cubicThetaAngularDirichletContinuation_gamma_functional hq x y hxy rev hk hs']
  simp only [norm_mul]
  calc
    _ = (‖ε‖*A)*‖metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s‖*
      ‖cubicThetaAngularDirichletContinuation q (-y) (-x) (!rev) k (1-s)‖ := by
        rw [←hfac]
        dsimp only [ε]
        ring
    _ ≤ (‖ε‖*A)*(G*(1+|s.im|)^(4*m))*B := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
