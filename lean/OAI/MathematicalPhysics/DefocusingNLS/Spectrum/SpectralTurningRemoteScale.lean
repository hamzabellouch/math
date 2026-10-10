import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! The frequency at twice the turning radius controls the remote scale chosen
in the paper, uniformly in angular degree and imaginary spectral parameter. -/

namespace DefocusingNLS

theorem spectralTurning_remote_scale (ell : ℕ) (h b omega r₀ : ℝ)
    (hh : h^2=1) (hb : 0≤b) (hb1 : b≤1) (hr₀ : 0<r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b
      ((ell : ℝ)*(ell+10)) omega r₀=0) :
    max ((ell : ℝ)+1) omega≤
      4*homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega (2*r₀) := by
  let L : ℝ := (ell : ℝ)*(ell+10)+99/4
  let A := r₀^2/16
  let H := L/r₀^2
  let K := A+H
  have hell : 0≤(ell : ℝ) := Nat.cast_nonneg ell
  have hL : 99/4≤L := by dsimp only [L]; nlinarith
  have hA : 0≤A := by dsimp only [A]; positivity
  have hH : 0≤H := by dsimp only [H]; positivity
  have hK : 0≤K := add_nonneg hA hH
  have hprod : A*H=L/16 := by dsimp only [A,H]; field_simp [hr₀.ne']
  have hK2 : L≤4*K^2 := by
    dsimp only [K]
    nlinarith [sq_nonneg (A-H)]
  have hK1 : 1≤K := by nlinarith
  have hLell : ((ell : ℝ)+1)^2≤L := by dsimp only [L]; nlinarith
  have hellK : (ell : ℝ)+1≤2*K := by nlinarith
  have hroot : A-H=h*omega-b := by
    dsimp only [A,H,L,homogeneousSpectralLocalizationFrequency] at *
    linarith only [hz]
  have homega : omega≤K+1 := by
    rcases sq_eq_one_iff.mp hh with he | he
    · rw [he,one_mul] at hroot
      dsimp only [K]
      linarith
    · rw [he,neg_one_mul] at hroot
      dsimp only [K]
      linarith
  have hSK : max ((ell : ℝ)+1) omega≤2*K := max_le hellK (by linarith)
  have hF : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega (2*r₀)=
      3*A+(3/4)*H := by
    rw [spectralTurningFrequency_identity h b ((ell : ℝ)*(ell+10)) omega r₀ (2*r₀)
      hr₀.ne' (mul_ne_zero (by norm_num) hr₀.ne') hz]
    dsimp only [A,H,L]
    field_simp
    ring
  rw [hF]
  dsimp only [K] at hSK
  linarith

end DefocusingNLS

end OAI
