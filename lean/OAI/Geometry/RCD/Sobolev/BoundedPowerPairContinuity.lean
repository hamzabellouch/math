import OAI.Geometry.RCD.Sobolev.ClippedPositivePower

namespace OAI

/-! # Continuous L2 pairings representing bounded product powers -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def boundedPowerPair (A B : ℝ≥0) (n : ℕ) (f g : Lp ℝ 2 μ) : ℝ :=
  inner ℝ ((clipped_positive_power_lipschitz A n).compLp (clipped_positive_power_zero A n) f)
    ((clipped_positive_power_lipschitz B n).compLp (clipped_positive_power_zero B n) g)

theorem boundedPowerPair_continuous (A B : ℝ≥0) (n : ℕ) :
    Continuous (fun fg : Lp ℝ 2 μ × Lp ℝ 2 μ => boundedPowerPair μ A B n fg.1 fg.2) :=
  (((clipped_positive_power_lipschitz A n).continuous_compLp
    (clipped_positive_power_zero A n)).comp continuous_fst).inner
    (((clipped_positive_power_lipschitz B n).continuous_compLp
      (clipped_positive_power_zero B n)).comp continuous_snd)

theorem boundedPowerPair_eq_integral (A B : ℝ≥0) (n : ℕ) (f g : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ A) (hg : ∀ᵐ x ∂μ, |g x| ≤ B) :
    boundedPowerPair μ A B n f g = ∫ x, (f x*g x)^(n+1) ∂μ := by
  rw [boundedPowerPair,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(clipped_positive_power_lipschitz A n).coeFn_compLp
    (clipped_positive_power_zero A n) f,
    (clipped_positive_power_lipschitz B n).coeFn_compLp
    (clipped_positive_power_zero B n) g,hf,hg] with x hx hy hfx hgx
  simp only [Real.inner_apply,hx,hy,Function.comp_apply,clipReal_eq_self _ hfx,
    clipReal_eq_self _ hgx,mul_pow]

end RegularPointCoordinates

end

end OAI
