import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import OAI.AlgebraicGeometry.PlaneCurves.Gluing

namespace OAI

/-!
# Scalar normalization of automorphic multipliers; Low- and high-degree coefficient-space correspondence
-/

section

/-! Explicit normalization of an arbitrary nonzero complex multiplier and
choice of a logarithmic frame with a nonintegral theta interval endpoint. -/
noncomputable section
namespace Nagata.W02

/-- Real exponent carrying the absolute value of the multiplier. -/
def multiplierSigma (τ : ℝ) (γ : ℂ) : ℝ := Real.log ‖γ‖ / Real.log τ

/-- Unit-norm phase, defined directly from the original multiplier. -/
def multiplierPhase (γ : ℂ) : ℂ := γ / (‖γ‖ : ℂ)

/-- The real scaling is exactly the multiplier norm. -/
theorem rpow_multiplierSigma {τ : ℝ} {γ : ℂ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    τ ^ multiplierSigma τ γ = ‖γ‖ := by
  have hl : Real.log τ ≠ 0 := ne_of_lt (Real.log_neg hτ hτ1)
  rw [Real.rpow_def_of_pos hτ, multiplierSigma]
  have hm : Real.log τ * (Real.log ‖γ‖ / Real.log τ) = Real.log ‖γ‖ :=
    mul_div_cancel₀ _ hl
  rw [hm, Real.exp_log (norm_pos_iff.mpr hγ)]

/-- The phase is genuinely unit norm, for every nonzero multiplier. -/
theorem norm_multiplierPhase {γ : ℂ} (hγ : γ ≠ 0) : ‖multiplierPhase γ‖ = 1 := by
  unfold multiplierPhase
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr hγ)]

/-- The original complex multiplier is recovered exactly, with all real/complex
coercions explicit. -/
theorem multiplier_factorization {τ : ℝ} {γ : ℂ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    γ = multiplierPhase γ * ((τ ^ multiplierSigma τ γ : ℝ) : ℂ) := by
  rw [rpow_multiplierSigma hτ hτ1 hγ]
  unfold multiplierPhase
  have hnorm : (‖γ‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hγ)
  exact (div_mul_cancel₀ γ hnorm).symm

/-- Frame center forcing the source interval's left endpoint to be one half. -/
def thetaFrameCenter (n σ : ℝ) : ℝ := (σ - 1 / 2) / n

theorem thetaFrameCenter_endpoint {n : ℝ} (hn : 0 < n) (σ : ℝ) :
    σ - thetaFrameCenter n σ * n = 1 / 2 := by
  unfold thetaFrameCenter
  rw [div_mul_cancel₀ _ (ne_of_gt hn)]
  ring

theorem half_not_integer : (1 / 2 : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have hz0 : (0 : ℤ) < z := by
    exact_mod_cast (show (0 : ℝ) < (z : ℝ) by rw [hz]; norm_num)
  have hz1 : z < (1 : ℤ) := by
    exact_mod_cast (show (z : ℝ) < 1 by rw [hz]; norm_num)
  omega

theorem thetaFrameCenter_nonintegral {n : ℝ} (hn : 0 < n) (σ : ℝ) :
    σ - thetaFrameCenter n σ * n ∉ Set.range (Int.cast : ℤ → ℝ) := by
  rw [thetaFrameCenter_endpoint hn]
  exact half_not_integer

/-- Fully explicit phase/exponent/frame choices for arbitrary γ in ℂ*. No
unit-norm or nonintegrality premise is left to the caller. -/
theorem exists_normalized_multiplier_frame {n τ : ℝ} {γ : ℂ}
    (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    ∃ (σ x0 : ℝ) (ε : ℂ), ‖ε‖ = 1 ∧
      γ = ε * ((τ ^ σ : ℝ) : ℂ) ∧
      σ - x0 * n = 1 / 2 ∧
      σ - x0 * n ∉ Set.range (Int.cast : ℤ → ℝ) := by
  exact ⟨multiplierSigma τ γ, thetaFrameCenter n (multiplierSigma τ γ), multiplierPhase γ,
    norm_multiplierPhase hγ, multiplier_factorization hτ hτ1 hγ,
    thetaFrameCenter_endpoint hn _, thetaFrameCenter_nonintegral hn _⟩

end Nagata.W02

end
end

section

/-!
# Scalar arithmetic of marked bundle presentations
-/
namespace Nagata.BundleArithmetic

/-- The degree of `T ⊗ A^(m-j)` is independent of j, because A has degree zero. -/
theorem coefficient_degree (d m j : ℝ) :
    3 * (d - 3 * m) + (m - j) * (3 * 3 - 9) = 3 * (d - 3 * m) := by
  ring

/-- Degree of the source of the second coefficient block. -/
theorem source_degree (d m j : ℝ) :
    3 * (d - 3 * j) = 3 * (d - 3 * m) - 9 * (j - m) := by
  ring

/-- Multiplication by the marked divisor raises that source degree to h. -/
theorem twisted_source_degree (d m j : ℝ) :
    3 * (d - 3 * j) + 9 * (j - m) = 3 * (d - 3 * m) := by
  ring

/-- Scalar exponent in the multiplier of `A = L^3 ⊗ O(-P)`. -/
theorem normal_minus_marked_exponent (s a : ℝ) :
    3 * ((s + a) / 3) - s = a := by
  ring

/-- The defining marked-point relation fixes the shifted exponent exactly. -/
theorem eta_shift (s a Δ x₀ : ℝ) (hs : s = 9 * x₀ - Δ) :
    (s + a) / 3 - 3 * x₀ = (a - Δ) / 3 := by
  rw [hs]
  ring

/-- Exponent identity for `T ⊗ A^m = L^d ⊗ O(-mP)`. -/
theorem total_bundle_exponent (d m s a : ℝ) :
    (d - 3 * m) * ((s + a) / 3) + m * a =
      d * ((s + a) / 3) - m * s := by
  ring

/-- Exponent compatibility of the positive-j source with the marked twist. -/
theorem twisted_source_exponent (d m j s a : ℝ) :
    (d - 3 * j) * ((s + a) / 3) + (j - m) * s =
      (d - 3 * m) * ((s + a) / 3) + (m - j) * a := by
  ring

/-- Subtracting x₀ times degree yields the first theta interval's U_j. -/
theorem first_interval_parameter (d m j s a Δ x₀ : ℝ)
    (hs : s = 9 * x₀ - Δ) :
    ((d - 3 * m) * ((s + a) / 3) + (m - j) * a) -
        x₀ * (3 * (d - 3 * m)) =
      (3 * (d - 3 * m)) / 9 * (a - Δ) + (m - j) * a := by
  rw [hs]
  ring

/-- The corresponding parameter for the second block's untwisted source. -/
theorem second_interval_parameter (d j s a Δ x₀ : ℝ)
    (hs : s = 9 * x₀ - Δ) :
    (d - 3 * j) * ((s + a) / 3) - x₀ * (3 * (d - 3 * j)) =
      (3 * (d - 3 * j)) / 9 * (a - Δ) := by
  rw [hs]
  ring

/-- At j=m the two interval formulas agree, including their length. -/
theorem interval_seam (d m a Δ : ℝ) :
    (3 * (d - 3 * m)) / 9 * (a - Δ) + (m - m) * a =
      (3 * (d - 3 * m)) / 9 * (a - Δ) := by
  ring

/-- The first block's interval is translated from the j=0 interval by -a*j. -/
theorem first_interval_translation (h m j a Δ : ℝ) :
    h / 9 * (a - Δ) + (m - j) * a =
      (h / 9 * (a - Δ) + m * a) - a * j := by
  ring

/-- The degree-zero index is the unique real solution of d-3j=0. -/
theorem degree_zero_index (d j : ℝ) (hz : d - 3 * j = 0) :
    j = d / 3 := by
  linarith

/-- With d>3m, the degree-zero block belongs to the second branch. -/
theorem degree_zero_after_m (d m j : ℝ) (hd : 3 * m < d)
    (hz : d - 3 * j = 0) : m < j := by
  linarith

/-- The j-coordinate of the tip in terms of h. -/
theorem degree_zero_tip_index (d m j : ℝ) (hz : d - 3 * j = 0) :
    j = m + (3 * (d - 3 * m)) / 9 := by
  linarith

/-- Both source interval endpoints collapse to K=0 at a zero-degree block. -/
theorem degree_zero_endpoints (d j a Δ : ℝ) (hz : d - 3 * j = 0) :
    (3 * (d - 3 * j)) / 9 * (a - Δ) = 0 ∧
      (3 * (d - 3 * j)) / 9 * (a - Δ) + 3 * (d - 3 * j) = 0 := by
  simp [hz]

/-- Integer indices with degree-zero source exist only at degrees divisible by 3. -/
theorem degree_zero_divisibility (d j : ℤ) (hz : d - 3 * j = 0) : 3 ∣ d := by
  refine ⟨j, ?_⟩
  exact sub_eq_zero.mp hz

/-- At most one integer index can contribute a degree-zero block. -/
theorem degree_zero_index_unique (d j k : ℤ)
    (hj : d - 3 * j = 0) (hk : d - 3 * k = 0) : j = k := by
  linarith

end Nagata.BundleArithmetic

end

section

namespace Nagata.CoefficientSpaces

/-- Fixed-frame multiplier identity for the source coefficient twisted by the
marked divisor. Unlike the real exponent identities, this is an equality of
actual complex transition multipliers with integer powers. -/
theorem coefficient_multiplier_identity {L Q : ℂ} (hL : L ≠ 0) (d m j : ℤ) :
    L ^ (d - 3 * j) * Q ^ (j - m) =
      L ^ (d - 3 * m) * normalMinusMarkedMultiplier L Q ^ (m - j) := by
  have hLpow : L ^ (d - 3 * m) * (L ^ (3 : ℕ)) ^ (m - j) = L ^ (d - 3 * j) := by
    rw [← zpow_natCast L 3, ← zpow_mul, ← zpow_add₀ hL]
    congr 1
    ring
  have hQpow : (Q ^ (m - j))⁻¹ = Q ^ (j - m) := by
    rw [← zpow_neg]
    congr 1
    ring
  rw [normalMinusMarkedMultiplier, div_zpow, div_eq_mul_inv, ← mul_assoc, hLpow, hQpow]

/-- The low-index quotient has exactly the common coefficient multiplier. -/
theorem quotient_coefficient_multiplier {L Q : ℂ} (hL : L ≠ 0) (d m j : ℤ) :
    L ^ (d - 3 * j) / Q ^ (m - j) =
      L ^ (d - 3 * m) * normalMinusMarkedMultiplier L Q ^ (m - j) := by
  rw [div_eq_mul_inv, ← zpow_neg]
  have he : -(m - j) = j - m := by ring
  rw [he]
  exact coefficient_multiplier_identity hL d m j

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces

/-- Every literal coefficient block lies in the common multiplier section space.
This proves the global transition compatibility of both source branches. -/
theorem coefficientSpace_le_common {τ L Q : ℂ} (hL : L ≠ 0)
    (d m j : ℤ) (P : ℂ → ℂ)
    (hP : P ∈ Nagata.W08.automorphicSections τ 9 Q) :
    coefficientSpace τ L Q d m j P ≤
      Nagata.W08.automorphicSections τ (3 * (d - 3 * m))
        (L ^ (d - 3 * m) * normalMinusMarkedMultiplier L Q ^ (m - j)) := by
  intro g hg
  by_cases hj : j ≤ m
  · simpa only [coefficientSpace, ite_eq_left hj] using hg
  · obtain ⟨f, hf, rfl⟩ := (mem_coefficientSpace_second (lt_of_not_ge hj)).mp hg
    have he : ((j - m).toNat : ℤ) = j - m :=
      Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hj)))
    have hdeg : 3 * (d - 3 * j) + ((j - m).toNat : ℤ) * 9 = 3 * (d - 3 * m) := by
      rw [he]
      ring
    have hgam : L ^ (d - 3 * j) * Q ^ (j - m).toNat =
        L ^ (d - 3 * m) * normalMinusMarkedMultiplier L Q ^ (m - j) := by
      rw [← zpow_natCast Q (j - m).toNat, he]
      exact coefficient_multiplier_identity hL d m j
    simpa only [hdeg, hgam] using multiplyPower_mem_sections hP hf (j - m).toNat

/-- Actual low-index division constructs a coefficient in V_j, including all
marked points: the source section's ordinary vanishing order supplies extension. -/
theorem exists_low_coefficient {τ L Q : ℂ} (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0)
    (d m j : ℤ) (hj : j ≤ m)
    (P : Nagata.W08.automorphicSections τ 9 Q)
    (f : Nagata.W08.automorphicSections τ (3 * (d - 3 * j)) (L ^ (d - 3 * j)))
    (hP : AnalyticOnNhd ℂ P.val {z | z ≠ 0})
    (hf : AnalyticOnNhd ℂ f.val {z | z ≠ 0})
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      ((m - j).toNat : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ g ∈ coefficientSpace τ L Q d m j P.val,
      ∀ z ≠ 0, f.val z = P.val z ^ (m - j).toNat * g z := by
  obtain ⟨G, hfactor⟩ := exists_automorphic_quotient hτ hQ f P hf hP (m - j).toNat hzero
  have he : ((m - j).toNat : ℤ) = m - j := Int.toNat_of_nonneg (sub_nonneg.mpr hj)
  have hdeg : 3 * (d - 3 * j) - ((m - j).toNat : ℤ) * 9 = 3 * (d - 3 * m) := by
    rw [he]
    ring
  have hgam : L ^ (d - 3 * j) / Q ^ (m - j).toNat =
      L ^ (d - 3 * m) * normalMinusMarkedMultiplier L Q ^ (m - j) := by
    rw [← zpow_natCast Q (m - j).toNat, he]
    exact quotient_coefficient_multiplier hL d m j
  refine ⟨G.val, ?_, hfactor⟩
  rw [coefficientSpace, ite_eq_left hj]
  simpa only [hdeg, hgam] using G.property

end Nagata.CoefficientSpaces

end

end OAI
