import OAI.MeasureTheory.Falconer.Recursion.ProjectionProfileAlgebra
import OAI.MeasureTheory.Falconer.Geometry.ProjectionGood

namespace OAI

/-! # Uniform projection averages for a finite-scale profile loss -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_projection_profile_mean {sig D A a : ℝ}
    (hsig : 0 < sig) (hD : 0 ≤ D) (hA : 1 ≤ A) (ha : 0 ≤ a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n ≤ N, ∀ k : ℝ, 0 ≤ k →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ]
        (ν : Measure (Sphere d)) [IsFiniteMeasure ν],
      (∀ᵐ x ∂μ, ‖x‖ ≤ D) → ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal
          (A*((2:ℝ)^N)^(k+a*sig)*r^((d:ℝ)/2))) →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      (∫⁻ w : Sphere d, projectionCollision μ (w:Space d)
        (2*((2:ℝ)^N)^(500*sig)/(2:ℝ)^n) ∂ν) ≤
      ENNReal.ofReal ((1/(2:ℝ)^n)*((2:ℝ)^N)^(k+(a+502)*sig)) := by
  obtain ⟨C,hC,hmean⟩ := averaged_projection_collision (d := d)
  let F := halfDimensionalShellConstant d*(Real.exp ((Real.pi^2/2)*D^2))^2
  have hF : 0 ≤ F := mul_nonneg (halfDimensionalShellConstant_nonneg d) (sq_nonneg _)
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  obtain ⟨N₁,hpoly⟩ := PlanarFalconer.fixed_linear_subpower
    (4*C+2*C*F*A) (by positivity) hsig
  obtain ⟨N₂,hscale⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 500*sig) (25/Real.pi)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN n hn k hk μ _ ν _ hsupport hmass hμ hν
  let R : ℝ := (2:ℝ)^N
  let H : ℝ := (2:ℝ)^n
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hH : 0 < H := by positivity
  have hK : 1 ≤ A*R^(k+a*sig) := one_le_mul_of_one_le_of_one_le hA
    (Real.one_le_rpow hR (by positivity))
  have hL : 1 ≤ R^sig := Real.one_le_rpow hR hsig.le
  have hscale' : 100/(2*R^(500*sig)/H) ≤ 2*Real.pi*H := by
    have hh : 25/Real.pi ≤ R^(500*sig) := hscale N ((le_max_right _ _).trans hN)
    have hp : 0 < R^(500*sig) := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    have hlow : 25 ≤ Real.pi*R^(500*sig) := by
      simpa only [mul_comm] using (div_le_iff₀ hpi).mp hh
    apply (div_le_iff₀ (by positivity : 0 < 2*R^(500*sig)/H)).mpr
    have he : (2*Real.pi*H)*(2*R^(500*sig)/H) = 4*(Real.pi*R^(500*sig)) := by
      field_simp
      ring
    rw [he]
    linarith
  have hm := hmean μ ν D R (A*R^(k+a*sig)) (R^sig) hD hsupport n
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn) hK hL hmass hμ hν
    (2*R^(500*sig)/H) (by positivity) hscale'
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  exact projection_profile_scalar_bound hR hH hC.le hF hA₀ hk ha hsig
    (Nat.cast_nonneg n) (by exact_mod_cast hn) (hpoly N ((le_max_left _ _).trans hN))

end Falconer

end OAI
