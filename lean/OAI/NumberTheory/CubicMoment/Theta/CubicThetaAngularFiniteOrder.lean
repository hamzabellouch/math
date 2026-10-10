import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularDirichletContinuation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularCompletedBounds
import OAI.NumberTheory.CubicMoment.Estimates.GammaInverseGrowth

namespace OAI

/-! Finite vertical order follows from bounded completed Mellin tails and
the already proved reciprocal-Gamma estimate. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem cubicThetaAngularDirichletContinuation_finiteOrder {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (rev : Bool) (k : ℕ) (a b : ℝ) :
    FiniteVerticalOrder (cubicThetaAngularDirichletContinuation q x y rev k) a b := by
  let ρ := cubicThetaLevelScale q
  let p : ℝ := 2*Real.pi
  have hρ : 0<ρ := cubicThetaLevelScale_pos hq
  have hp : 0<p := by dsimp [p]; positivity
  let P : ℝ→ℝ := fun σ => 4*ρ^(2*σ+(k:ℝ)-1)*p^(2*σ+(k:ℝ))
  have hP : Continuous P := by
    have hA : Continuous (fun σ : ℝ => 2*σ+(k:ℝ)-1) := by fun_prop
    have hB : Continuous (fun σ : ℝ => 2*σ+(k:ℝ)) := by fun_prop
    exact (continuous_const.mul ((Real.continuous_const_rpow hρ.ne').comp
      hA)).mul ((Real.continuous_const_rpow hp.ne').comp hB)
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hP.continuousOn
  let D := max M 0
  have hD : 0≤D := le_max_right _ _
  have hPb (σ : ℝ) (hσ : σ∈Icc a b) : P σ≤D :=
    (le_abs_self _).trans ((hM σ hσ).trans (le_max_left _ _))
  obtain ⟨B₁,hB₁,hΓ₁⟩ := gammaInverseFiniteOrder (a+(k:ℝ)/2+1/6) (b+(k:ℝ)/2+1/6)
  obtain ⟨B₂,hB₂,hΓ₂⟩ := gammaInverseFiniteOrder (a+(k:ℝ)/2-1/6) (b+(k:ℝ)/2-1/6)
  obtain ⟨C,hC,hF⟩ := cubicThetaLevelAngularCompleted_bounded_strip hq x y rev k
    (2*a+(k:ℝ)-1) (2*b+(k:ℝ)-1)
  let K := D*C
  have hK : 0≤K := mul_nonneg hD hC
  refine ⟨K+B₁+B₂,2,by positivity,?_⟩
  intro s hs
  have hG₁ : ‖(Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹‖≤Real.exp (B₁*(1+|s.im|)^2) := by
    have H := hΓ₁ (s+(k:ℂ)/2+1/6) (by
      simp only [mem_Icc,Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
      constructor <;> linarith [hs.1,hs.2])
    simpa only [Complex.add_im,Complex.div_ofNat_im,Complex.natCast_im,Complex.one_im,
      zero_div,add_zero] using H
  have hG₂ : ‖(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹‖≤Real.exp (B₂*(1+|s.im|)^2) := by
    have H := hΓ₂ (s+(k:ℂ)/2-1/6) (by
      simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
      constructor <;> linarith [hs.1,hs.2])
    simpa only [Complex.add_im,Complex.sub_im,Complex.div_ofNat_im,Complex.natCast_im,
      Complex.one_im,zero_div,add_zero,sub_zero] using H
  have hF' : ‖cubicThetaLevelAngularCompleted q x y rev k (2*s+(k:ℂ)-1)‖≤C := by
    apply hF
    simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.re_ofNat,
      Complex.im_ofNat,Complex.natCast_re,Complex.one_re,zero_mul,sub_zero]
    constructor <;> linarith [hs.1,hs.2]
  have hpref : ‖4*(ρ:ℂ)^(2*s+(k:ℂ)-1)*(p:ℂ)^(2*s+(k:ℂ))‖≤D := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hρ,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.norm_ofNat,Complex.add_re,Complex.sub_re,Complex.mul_re,
      Complex.re_ofNat,Complex.im_ofNat,Complex.natCast_re,Complex.one_re,zero_mul,sub_zero]
    exact hPb s.re hs
  have he : cubicThetaAngularDirichletContinuation q x y rev k s=
      (4*(ρ:ℂ)^(2*s+(k:ℂ)-1)*(p:ℂ)^(2*s+(k:ℂ)))*
        (Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹*(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹*
          cubicThetaLevelAngularCompleted q x y rev k (2*s+(k:ℂ)-1) := rfl
  have hQ : 1≤(1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  calc
    _ ≤ (D*Real.exp (B₁*(1+|s.im|)^2))*Real.exp (B₂*(1+|s.im|)^2)*C := by
      rw [he,norm_mul,norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul (mul_le_mul hpref hG₁ (_root_.norm_nonneg _) hD)
        hG₂ (_root_.norm_nonneg _) (by positivity)) hF' (_root_.norm_nonneg _) (by positivity)
    _ = K*Real.exp ((B₁+B₂)*(1+|s.im|)^2) := by
      rw [add_mul,Real.exp_add]
      dsimp [K]
      ring
    _ ≤ Real.exp K*Real.exp ((B₁+B₂)*(1+|s.im|)^2) :=
      mul_le_mul_of_nonneg_right (le_trans (by linarith : K≤K+1) (Real.add_one_le_exp K)) (Real.exp_pos _).le
    _ = Real.exp (K+(B₁+B₂)*(1+|s.im|)^2) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hQ hK]

end CubicFirstMoment

end

end OAI
