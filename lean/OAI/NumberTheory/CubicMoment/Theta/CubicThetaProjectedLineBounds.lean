import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedFunctional
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDirichletBounds
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticGammaRecurrence

namespace OAI

/-! Absolute initial-line bounds and the far-left bound needed to
move the actual selected-series Mellin contour. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaProjectedDirichlet_right_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {σ : ℝ} (hσ : 3/2<σ) (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaProjectedDirichlet g hc rev k s‖≤243*cubicThetaDirichletNormMass (2*σ-1) := by
  rw [cubicThetaProjectedDirichlet_initial g hc rev hk (by linarith)]
  apply cubicThetaDirichlet_norm_le (fun n hn => ?_) (by linarith : 2<2*σ-1) _ (by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      Complex.one_re,zero_mul,sub_zero,hs])
  rw [norm_mul,norm_theta hn,one_mul,cubicThetaCoefficientTwist_norm]
  exact cubicThetaProjectedCoefficient_bound g hc n

theorem cubicThetaSelectedDirichlet_right_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {σ : ℝ} (hσ : 3/2<σ) (s : ℂ) (hs : s.re=σ) :
    ‖cubicThetaSelectedDirichlet g hc rev k s‖≤81*cubicThetaDirichletNormMass (2*σ-1) := by
  rw [cubicThetaSelectedDirichlet_initial g hc rev hk (by linarith)]
  apply cubicThetaDirichlet_norm_le (fun n hn => ?_) (by linarith : 2<2*σ-1) _ (by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      Complex.one_re,zero_mul,sub_zero,hs])
  rw [norm_mul,norm_theta hn,one_mul,cubicThetaCoefficientTwist_norm]
  exact cubicThetaSelectedCoefficient_norm n

theorem cubicThetaSelectedDirichlet_left_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {m : ℕ} (hm : 2 ≤ m) : ∃ C : ℝ, 0≤C ∧ ∀ s : ℂ,s.re=1/2-(m:ℝ) →
      ‖cubicThetaSelectedDirichlet g hc rev k s‖≤C*(1+|s.im|)^(4*m) := by
  obtain ⟨G,hG,hΓ⟩ := metaplecticGamma_half_integer_bound (cubicThetaCircleOrder (!rev) k) m
  let q := g 1 0
  let A := cubicThetaLevelScale q^(-4*(m:ℝ))*(2*Real.pi)^(-4*(m:ℝ))
  let B := 243*cubicThetaDirichletNormMass (2*(m:ℝ))
  let ε := (cubicThetaLevelAngularRoot q rev k)⁻¹
  have hA : 0≤A := mul_nonneg (Real.rpow_nonneg (cubicThetaLevelScale_pos hc).le _)
    (Real.rpow_nonneg (by positivity) _)
  have hB : 0≤B := mul_nonneg (by norm_num) (cubicThetaDirichletNormMass_nonneg _)
  refine ⟨‖ε‖*A*G*B,by positivity,?_⟩
  intro s hs
  have hmR : (2:ℝ)≤ m := by exact_mod_cast hm
  have he : s=(1/2:ℂ)-(m:ℂ)+(s.im:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [hs]
  have hgamma : ‖metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s‖≤G*(1+|s.im|)^(4*m) := by
    rw [he]
    simpa using hΓ s.im
  have hdual := cubicThetaProjectedDirichlet_right_bound g hc rev hk
    (σ:=1/2+(m:ℝ)) (by linarith) (1-s) (by simp [hs]; ring)
  have hb : ‖cubicThetaProjectedDirichlet g hc rev k (1-s)‖≤B := by
    simpa only [show 2*(1/2+(m:ℝ))-1=2*(m:ℝ) by ring] using hdual
  have hpow : (4*s-2).re= -4*(m:ℝ) := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,hs]
    ring
  have hfac : ‖(cubicThetaLevelScale q:ℂ)^(4*s-2)‖*‖((2*Real.pi:ℝ):ℂ)^(4*s-2)‖=A := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (cubicThetaLevelScale_pos hc),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<2*Real.pi),hpow]
  have hs' : s.re<5/6+(k:ℝ)/2 := by
    have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
    linarith
  rw [cubicThetaSelectedDirichlet_gamma g hc rev hk hs']
  simp only [norm_mul]
  calc
    _ = (‖ε‖*A)*‖metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s‖*
      ‖cubicThetaProjectedDirichlet g hc rev k (1-s)‖ := by
        rw [←hfac]
        dsimp only [ε,q]
        ring
    _ ≤ (‖ε‖*A)*(G*(1+|s.im|)^(4*m))*B := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
