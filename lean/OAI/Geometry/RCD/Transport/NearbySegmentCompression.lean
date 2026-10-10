import OAI.Geometry.RCD.Metric.NearbySmallBallMass
import OAI.Geometry.RCD.Harmonic.DefectSegment

namespace OAI

/-! # Compression cost for small endpoint balls

The local segment estimate must be uniform when its endpoints move. The
actual Bishop--Gromov lower bound controls both endpoint normalizations.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem inverse_mass_le_of_scaled_lower {M a D s : ℝ}
    (ha : 0 < a) (hMs : 0 < M*s) (hlower : M*s ≤ D*a) :
    a⁻¹ ≤ D/(M*s) := by
  apply (le_div_iff₀ hMs).mpr
  calc
    a⁻¹*(M*s) = (M*s)/a := by ring
    _ ≤ D := (div_le_iff₀ ha).mpr hlower

theorem NoncollapsedRCD.endpoint_ball_compression_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p x y : X} {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hx : dist x p ≤ R) (hy : dist y p ≤ R)
    (hcurv : -1 ≤ K*(2*R)^2) :
    (max ((hausdorff n X) (ball x ρ))⁻¹ ((hausdorff n X) (ball y ρ))⁻¹).toReal ≤
      ((Real.cosh 1^(n-1)*2^n)*R^n)/((hausdorff n X).real (ball p R)*ρ^n) := by
  let μ := hausdorff n X
  have hM : 0 < μ.real (ball p R) := ENNReal.toReal_pos
    (hX.fullSupport p R hR).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have ha : 0 < μ.real (ball x ρ) := ENNReal.toReal_pos
    (hX.fullSupport x ρ hρ).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hb : 0 < μ.real (ball y ρ) := ENNReal.toReal_pos
    (hX.fullSupport y ρ hρ).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hxa := inverse_mass_le_of_scaled_lower ha (mul_pos hM (pow_pos hρ n))
    (hX.nearby_small_ball_mass hn hR hx hρ hρR hcurv)
  have hyb := inverse_mass_le_of_scaled_lower hb (mul_pos hM (pow_pos hρ n))
    (hX.nearby_small_ball_mass hn hR hy hρ hρR hcurv)
  by_cases hxy : μ (ball x ρ) ≤ μ (ball y ρ)
  · rw [max_eq_left (ENNReal.inv_le_inv.mpr hxy),ENNReal.toReal_inv]
    exact hxa
  · rw [max_eq_right (ENNReal.inv_le_inv.mpr (le_of_not_ge hxy)),ENNReal.toReal_inv]
    exact hyb

theorem compressionBudget_le_of_rescaled_curvature {K R : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hK : K ≤ 0) (hcurv : -1 ≤ K*(4*R)^2)
    (C : ℝ≥0∞) :
    (compressionBudget K n (2*R) C).toReal ≤ Real.exp (n:ℝ)*C.toReal := by
  have hn1 : 1 ≤ (n:ℝ)-1 := by
    have hh : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn1pos : 0 < (n:ℝ)-1 := lt_of_lt_of_le zero_lt_one hn1
  have hKbound : |K| * (4*R)^2 ≤ 1 := by rw [abs_of_nonpos hK]; nlinarith
  have hs : (4*R*Real.sqrt (|K|/((n:ℝ)-1)))^2 ≤ 1 := by
    rw [mul_pow,Real.sq_sqrt (div_nonneg (abs_nonneg K) hn1pos.le)]
    have heq : (4*R)^2*(|K|/((n:ℝ)-1)) = (|K| * (4*R)^2)/((n:ℝ)-1) := by ring
    rw [heq]
    exact (div_le_one hn1pos).mpr (hKbound.trans hn1)
  have hroot : 4*R*Real.sqrt (|K|/((n:ℝ)-1)) ≤ 1 := by nlinarith
  have hexp : Real.exp ((n:ℝ)*(4*R)*Real.sqrt (|K|/((n:ℝ)-1))) ≤
      Real.exp (n:ℝ) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg n : (0:ℝ)≤n)
    nlinarith only [hh]
  simp only [compressionBudget,compressionStep,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have heq : (2:ℝ)*(2*R)=4*R := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg

end RegularPointCoordinates

end

end OAI
