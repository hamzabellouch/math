import OAI.MeasureTheory.Falconer.Radial.RadialAngleCaps
import OAI.MeasureTheory.Falconer.Recursion.TruncatedScalarPotential

namespace OAI

/-! # Radial caps bound the singular part of the endpoint triple kernel -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem radial_angle_potential (μ : Measure (Space n)) (G : Set (Space n × Space n))
    (p q : Space n) (hq : q ≠ p) (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    {K s ℓ : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsℓ : s < ℓ) (g k : ℕ)
    (hcap : ∀ j : ℕ, j ≤ g+k → ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ)) :
    (∫⁻ z in {z | displacementAngle p q z < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (displacementAngle p q z) (1/(2:ℝ)^(g+k)))^s)
        ∂μ.restrict {z | (p,z) ∈ G}) ≤
      ENNReal.ofReal ((2:ℝ)^s*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^(s-ℓ))*
        (1+(2:ℝ)^s/(1-(2:ℝ)^(s-ℓ))))) := by
  have hsmall (j : ℕ) (hj : j ≤ g+k) :
      (μ.restrict {z | (p,z) ∈ G}) {z | displacementAngle p q z < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((2*K*(3:ℝ)^ℓ)*(1/(2:ℝ)^j)^ℓ) := by
    rw [Measure.restrict_apply (measurableSet_lt (displacementAngle_measurable p q) measurable_const)]
    calc
      _ ≤ μ {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ 1/(2:ℝ)^j} := by
        apply measure_mono
        rintro z ⟨hz,hG⟩
        exact ⟨hG,hz.le⟩
      _ ≤ 2*ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ) :=
        radial_angle_sublevel μ G p q hq hdiag (by positivity) (hcap j hj)
      _ = _ := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num),Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        ring
  exact truncated_scalar_potential (μ.restrict {z | (p,z) ∈ G})
    (displacementAngle p q) (displacementAngle_measurable p q)
    (displacementAngle_nonneg p q) (by positivity) hs hsℓ g k hsmall

end Falconer

end OAI
