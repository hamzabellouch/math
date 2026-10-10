import OAI.Geometry.RCD.Sobolev.CenteredAffineSobolev
import OAI.Geometry.RCD.Sobolev.AffineCoefficientEnergy

namespace OAI

/-! # Recovering affine coefficient errors from two actual fits -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem centeredAffineSobolev_difference_constant {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s : Set X)
    (η ζ : SobolevSpace μ hQ) (v a b : Euclidean n)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ))
    (hζ : SobolevSpace.toLp μ hQ ζ =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) :
    SobolevSpace.toLp μ hQ
      ((centeredAffineSobolev μ hQ u η v a - centeredAffineSobolev μ hQ u ζ v b) -
        sobolevColumnMap μ hQ u (a - b)) =ᵐ[μ.restrict s] fun _ => -⟪v, a - b⟫_ℝ := by
  have hid : (centeredAffineSobolev μ hQ u η v a - centeredAffineSobolev μ hQ u ζ v b) -
      sobolevColumnMap μ hQ u (a - b) = (-⟪v, a⟫_ℝ) • η - (-⟪v, b⟫_ℝ) • ζ := by
    rw [centeredAffineSobolev, centeredAffineSobolev, map_sub]
    abel
  rw [hid]
  change SobolevSpace.toLpCLM μ hQ ((-⟪v, a⟫_ℝ) • η - (-⟪v, b⟫_ℝ) • ζ) =ᵐ[μ.restrict s] _
  rw [map_sub, map_smul, map_smul]
  filter_upwards [hη, hζ, ae_restrict_of_ae (Lp.coeFn_sub
      ((-⟪v, a⟫_ℝ) • SobolevSpace.toLp μ hQ η) ((-⟪v, b⟫_ℝ) • SobolevSpace.toLp μ hQ ζ)),
    ae_restrict_of_ae (Lp.coeFn_smul (-⟪v, a⟫_ℝ) (SobolevSpace.toLp μ hQ η)),
    ae_restrict_of_ae (Lp.coeFn_smul (-⟪v, b⟫_ℝ) (SobolevSpace.toLp μ hQ ζ))]
    with x hx hy hs ha hb
  change ((-⟪v, a⟫_ℝ) • SobolevSpace.toLp μ hQ η -
    (-⟪v, b⟫_ℝ) • SobolevSpace.toLp μ hQ ζ) x = -⟪v, a - b⟫_ℝ
  rw [hs]
  simp only [Pi.sub_apply, ha, hb, Pi.smul_apply, smul_eq_mul, hx, hy, mul_one,
    inner_sub_right]
  ring

/-- Two approximations to the same local target control their difference.
The two compact constant representatives may be different. -/
theorem normalized_two_fit_difference {s : Set X} (hfin : μ s ≠ ∞)
    (t : Lp ℝ 2 (μ.restrict s)) (f g : SobolevSpace μ hQ) {A B : ℝ}
    (hf : ‖normalizeLocalL2 μ s hfin (t - SobolevSpace.restrictLp μ hQ s f)‖ ^ 2 ≤ A)
    (hg : ‖normalizeLocalL2 μ s hfin (t - SobolevSpace.restrictLp μ hQ s g)‖ ^ 2 ≤ B) :
    ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (f - g))‖ ^ 2 ≤
      2 * A + 2 * B := by
  let x := normalizeLocalL2 μ s hfin (t - SobolevSpace.restrictLp μ hQ s g)
  let y := normalizeLocalL2 μ s hfin (t - SobolevSpace.restrictLp μ hQ s f)
  have heq : normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (f - g)) = x - y := by
    dsimp only [x, y, normalizeLocalL2]
    rw [map_sub, ← smul_sub]
    congr 1
    abel
  rw [heq]
  have hh := norm_sub_le x y
  have hh2 := (sq_le_sq₀ (norm_nonneg (x - y))
    (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr hh
  change ‖y‖ ^ 2 ≤ A at hf
  change ‖x‖ ^ 2 ≤ B at hg
  nlinarith only [hf, hg, hh2, sq_nonneg (‖x‖ - ‖y‖)]

end RegularPointCoordinates

end

end OAI
