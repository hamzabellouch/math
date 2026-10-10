import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitCoefficients

namespace OAI

/-! A quantitative Lipschitz constant for the spectral coefficient pair.
It tends to zero on a fixed subunit disk, even after division by the
exponential order of the profile remainder. -/

open Filter Topology
namespace DefocusingNLS

theorem spectral_power_difference_bound (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (z w : ℂ) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖z^n-w^n‖ ≤ ((n : ℝ)*ρ^n/ρ)*‖z-w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z^(n+1)-w^(n+1)=z^n*(z-w)+(z^n-w^n)*w := by ring
    rw [he]
    calc
      _ ≤ ‖z^n*(z-w)‖+‖(z^n-w^n)*w‖ := norm_add_le _ _
      _ = ‖z‖^n*‖z-w‖+‖z^n-w^n‖*‖w‖ := by simp only [norm_mul,norm_pow]
      _ ≤ ρ^n*‖z-w‖+(((n : ℝ)*ρ^n/ρ)*‖z-w‖)*ρ := by
        gcongr
      _ = (((n+1 : ℕ) : ℝ)*ρ^(n+1)/ρ)*‖z-w‖ := by
        rw [pow_succ,Nat.cast_add,Nat.cast_one]
        field_simp
        ring

theorem spectral_mixed_power_difference_bound (a b : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (z w : ℂ) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖z^a*(star z)^b-w^a*(star w)^b‖ ≤ (((a+b : ℕ) : ℝ)*ρ^(a+b)/ρ)*‖z-w‖ := by
  have hp := spectral_power_difference_bound a ρ hρ z w hz hw
  have hs := spectral_power_difference_bound b ρ hρ (star z) (star w)
    (by simpa only [norm_star] using hz) (by simpa only [norm_star] using hw)
  simp only [← star_sub,norm_star] at hs
  have he : z^a*(star z)^b-w^a*(star w)^b=
      (z^a-w^a)*(star z)^b+w^a*((star z)^b-(star w)^b) := by ring
  rw [he]
  calc
    _ ≤ ‖(z^a-w^a)*(star z)^b‖+‖w^a*((star z)^b-(star w)^b)‖ := norm_add_le _ _
    _ = ‖z^a-w^a‖*‖z‖^b+‖w‖^a*‖(star z)^b-(star w)^b‖ := by
      simp only [norm_mul,norm_pow,norm_star]
    _ ≤ (((a : ℝ)*ρ^a/ρ)*‖z-w‖)*ρ^b+ρ^a*(((b : ℝ)*ρ^b/ρ)*‖z-w‖) := by
      gcongr
    _ = _ := by rw [pow_add,Nat.cast_add]; ring

theorem spectralCoefficient_subunit_difference (m : ℕ) (hm : 1 ≤ m)
    (ρ : ℝ) (hρ : 0 < ρ) (z w : ℂ) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖spectralDiagonalCoefficient m z-spectralDiagonalCoefficient m w‖+
      ‖spectralCrossCoefficient m z-spectralCrossCoefficient m w‖ ≤
      (2*(m : ℝ)*(2*(m : ℝ)+1)*ρ^(2*m)/ρ)*‖z-w‖ := by
  have hp := spectral_mixed_power_difference_bound m m ρ hρ z w hz hw
  have hmixed := spectral_mixed_power_difference_bound (m+1) (m-1) ρ hρ z w hz hw
  have he : m+1+(m-1)=2*m := by omega
  have he' : m+m=2*m := by omega
  rw [he'] at hp
  rw [he] at hmixed
  have hdiag : ‖spectralDiagonalCoefficient m z-spectralDiagonalCoefficient m w‖ ≤
      ((m : ℝ)+1)*(((2*m : ℕ) : ℝ)*ρ^(2*m)/ρ)*‖z-w‖ := by
    have heq : spectralDiagonalCoefficient m z-spectralDiagonalCoefficient m w=
        ((m+1 : ℕ) : ℂ)*(z^m*(star z)^m-w^m*(star w)^m) := by
      simp only [spectralDiagonalCoefficient]
      ring
    rw [heq,norm_mul,Complex.norm_natCast,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ ((m : ℝ)+1)*((((2*m : ℕ) : ℝ)*ρ^(2*m)/ρ)*‖z-w‖) := by gcongr
      _ = _ := by ring
  have hcross : ‖spectralCrossCoefficient m z-spectralCrossCoefficient m w‖ ≤
      (m : ℝ)*(((2*m : ℕ) : ℝ)*ρ^(2*m)/ρ)*‖z-w‖ := by
    have heq : spectralCrossCoefficient m z-spectralCrossCoefficient m w=
        (m : ℂ)*(z^(m+1)*(star z)^(m-1)-w^(m+1)*(star w)^(m-1)) := by
      simp only [spectralCrossCoefficient]
      ring
    rw [heq,norm_mul,Complex.norm_natCast]
    calc
      _ ≤ (m : ℝ)*((((2*m : ℕ) : ℝ)*ρ^(2*m)/ρ)*‖z-w‖) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ((m : ℝ)+1)*(((2*m : ℕ) : ℝ)*ρ^(2*m)/ρ)*‖z-w‖+
        (m : ℝ)*(((2*m : ℕ) : ℝ)*ρ^(2*m)/ρ)*‖z-w‖ := add_le_add hdiag hcross
    _ = _ := by push_cast; ring

theorem spectralCoefficient_difference_rate_tendsto (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℕ => 2*(n : ℝ)*(2*(n : ℝ)+1)*ρ^(2*n)/ρ) atTop (𝓝 0) := by
  have hq : ρ^2 < 1 := pow_lt_one₀ hρ.le hρ1 (by decide : 2 ≠ 0)
  have h₂ := tendsto_pow_const_mul_const_pow_of_lt_one 2 (sq_nonneg ρ) hq
  have h₁ := tendsto_self_mul_const_pow_of_lt_one (sq_nonneg ρ) hq
  convert ((h₂.const_mul 4).add (h₁.const_mul 2)).div_const ρ using 1
  · funext n
    rw [pow_mul]
    ring
  · norm_num

theorem spectralCoefficient_weighted_difference (m : ℕ) (hm : 1 ≤ m)
    (ρ : ℝ) (hρ : 0 < ρ) (q p e : ℂ) (κ t : ℝ)
    (hq : ‖q‖ ≤ ρ) (hp : ‖p‖ ≤ ρ)
    (he : q-p=(Real.exp (-κ*t) : ℂ)*e) :
    ‖(Real.exp (κ*t) : ℂ)*(spectralDiagonalCoefficient m q-spectralDiagonalCoefficient m p)‖+
      ‖(Real.exp (κ*t) : ℂ)*(spectralCrossCoefficient m q-spectralCrossCoefficient m p)‖ ≤
      (2*(m : ℝ)*(2*(m : ℝ)+1)*ρ^(2*m)/ρ)*‖e‖ := by
  have hb := spectralCoefficient_subunit_difference m hm ρ hρ q p hq hp
  have hn : ‖q-p‖=Real.exp (-κ*t)*‖e‖ := by
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (κ*t))
  have hexp : Real.exp (κ*t)*Real.exp (-κ*t)=1 := by rw [← Real.exp_add]; simp
  rw [hn] at hh
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (κ*t)*(‖spectralDiagonalCoefficient m q-spectralDiagonalCoefficient m p‖+
        ‖spectralCrossCoefficient m q-spectralCrossCoefficient m p‖) := by ring
    _ ≤ Real.exp (κ*t)*((2*(m : ℝ)*(2*(m : ℝ)+1)*ρ^(2*m)/ρ)*(Real.exp (-κ*t)*‖e‖)) := hh
    _ = (Real.exp (κ*t)*Real.exp (-κ*t))*
        (2*(m : ℝ)*(2*(m : ℝ)+1)*ρ^(2*m)/ρ)*‖e‖ := by ring
    _ = _ := by rw [hexp,one_mul]

theorem radialShooting_spectralDifference_uniform_small :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∃ δ : ℕ → ℝ,
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ z : ProfileCertificate.ProfileMatchingBall, ∀ t : ℝ,
        Real.log innerBoundaryRadius ≤ t → ∀ p : ℂ, ‖p‖ ≤ ρ →
          let q := (radialExteriorCanonical (radialShootingNu n z) n (radialShootingM z)
            (Real.log innerBoundaryRadius) t).1
          ‖spectralDiagonalCoefficient n q-spectralDiagonalCoefficient n p‖+
            ‖spectralCrossCoefficient n q-spectralCrossCoefficient n p‖ ≤ δ n*‖q-p‖ := by
  obtain ⟨κ,σ,hκ,hσ,he⟩ := radialShooting_uniform_annulus
  let ρ := max σ (1/2)
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ1 : ρ < 1 := max_lt hσ (by norm_num)
  refine ⟨ρ,hρ,hρ1,fun n => 2*(n : ℝ)*(2*(n : ℝ)+1)*ρ^(2*n)/ρ,
    fun n => by positivity,spectralCoefficient_difference_rate_tendsto ρ hρ hρ1,?_⟩
  filter_upwards [he,eventually_ge_atTop 1] with n hn hmn z t ht p hp
  exact spectralCoefficient_subunit_difference n hmn ρ hρ _ p
    ((hn z t ht).2.trans (le_max_left _ _)) hp

end DefocusingNLS

end OAI
