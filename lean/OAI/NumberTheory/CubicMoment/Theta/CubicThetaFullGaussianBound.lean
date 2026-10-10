import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullGaussian

namespace OAI

/-! Uniform control of the affine four-dimensional heat kernel by its
zero Fourier mode. Both errors come from explicit nonzero lattice vectors. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullGaussian_row_error {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    |cubicThetaFullGaussian p t-
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*cubicThetaScalarGaussianReal 0 (t*p.2)| ≤
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*
        cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))*
          cubicThetaScalarGaussianReal 0 (t*p.2) := by
  let E : Eisenstein → ℝ := fun a => Real.exp (-9*t*p.2*norm a)
  let G : Eisenstein → ℝ := fun a =>
    cubicThetaScalarGaussianReal (3*(a:ℂ)*p.1+1) (t/p.2)
  let K := 2*Real.pi/(9*Real.sqrt 3*(t/p.2))
  let T := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))
  have hK : 0≤K := by dsimp [K]; positivity
  have hT : 0≤T := cubicThetaLatticeGaussianTail_nonneg _
  have hE : Summable E := by
    convert cubicThetaScalarGaussianReal_summable 0 (mul_pos ht hp) using 1
    funext a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    dsimp [E]
    congr 1
    ring
  have hEsum : ∑' a,E a=cubicThetaScalarGaussianReal 0 (t*p.2) := by
    unfold cubicThetaScalarGaussianReal
    apply tsum_congr
    intro a
    rw [cubicThetaScalarGaussianReal_zero_summand]
    dsimp [E]
    congr 1
    ring
  have hG (a : Eisenstein) : 0≤G a := cubicThetaScalarGaussianReal_nonneg _ _
  have hGu (a : Eisenstein) : G a≤K*(1+T) :=
    cubicThetaScalarGaussianReal_le _ (div_pos ht hp)
  have hGe (a : Eisenstein) : |G a-K|≤K*T :=
    cubicThetaScalarGaussianReal_error _ (div_pos ht hp)
  have hF : Summable (fun a => E a*G a) := by
    apply (hE.mul_right (K*(1+T))).of_nonneg_of_le
    · intro a
      exact mul_nonneg (Real.exp_pos _).le (hG a)
    · intro a
      exact mul_le_mul_of_nonneg_left (hGu a) (Real.exp_pos _).le
  have hEK := hE.mul_right K
  have hD : Summable (fun a => E a*(G a-K)) := by
    simpa only [mul_sub] using hF.sub hEK
  have hmajor := hE.mul_right (K*T)
  rw [cubicThetaFullGaussian_reindex hp ht]
  change |(∑' a,E a*G a)-K*cubicThetaScalarGaussianReal 0 (t*p.2)|≤_
  rw [←hEsum,mul_comm K,←tsum_mul_right,←hF.tsum_sub hEK]
  calc
    _ = ‖∑' a,E a*(G a-K)‖ := by simp only [mul_sub,Real.norm_eq_abs]
    _ ≤ ∑' a,‖E a*(G a-K)‖ := norm_tsum_le_tsum_norm hD.norm
    _ ≤ ∑' a,E a*(K*T) := by
      apply hD.norm.tsum_le_tsum _ hmajor
      intro a
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hGe a) (Real.exp_pos _).le
    _ = _ := by rw [tsum_mul_right,hEsum]; ring

lemma cubicThetaFullGaussian_error {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    |cubicThetaFullGaussian p t-
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*(2*Real.pi/(9*Real.sqrt 3*(t*p.2)))| ≤
      (2*Real.pi/(9*Real.sqrt 3*(t/p.2)))*(2*Real.pi/(9*Real.sqrt 3*(t*p.2)))*
        (cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))*
          (1+cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2))))+
          cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2)))) := by
  let K := 2*Real.pi/(9*Real.sqrt 3*(t/p.2))
  let L := 2*Real.pi/(9*Real.sqrt 3*(t*p.2))
  let T := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))
  let U := cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2)))
  let g := cubicThetaScalarGaussianReal 0 (t*p.2)
  have hK : 0≤K := by dsimp [K]; positivity
  have hT : 0≤T := cubicThetaLatticeGaussianTail_nonneg _
  have he : |g-L|≤L*U := cubicThetaScalarGaussianReal_error 0 (mul_pos ht hp)
  have hg : g≤L*(1+U) := cubicThetaScalarGaussianReal_le 0 (mul_pos ht hp)
  have hr : |cubicThetaFullGaussian p t-K*g|≤K*T*g := cubicThetaFullGaussian_row_error hp ht
  change |cubicThetaFullGaussian p t-K*L|≤K*L*(T*(1+U)+U)
  calc
    _ = |(cubicThetaFullGaussian p t-K*g)+K*(g-L)| := by congr 1; ring
    _ ≤ |cubicThetaFullGaussian p t-K*g|+|K*(g-L)| := abs_add_le _ _
    _ ≤ K*T*g+K*(L*U) := by
      rw [abs_mul,abs_of_nonneg hK]
      exact add_le_add hr (mul_le_mul_of_nonneg_left he hK)
    _ ≤ K*T*(L*(1+U))+K*(L*U) :=
      add_le_add (mul_le_mul_of_nonneg_left hg (mul_nonneg hK hT)) le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
