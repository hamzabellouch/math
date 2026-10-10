import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveIncrementBounds
import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScaleAlgebra

namespace OAI

/-! Derivative and positional two-jet bounds for the actual slow-map
increment.  Position coordinates cancel before the two-derivative estimate
is applied. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open WeightedEstimates JetPolynomial

lemma lowJet_increment_eq_variation {G H : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    lowJet (fun x => G x + H x) - lowJet G = variationLowJet H := by
  funext x
  have he : lowJet (fun y => G y + H y) x = lowJet G x + variationLowJet H x := by
    simpa only [one_smul] using lowJet_affine hG hH 1 x
  change lowJet (fun y => G y + H y) x - lowJet G x = _
  rw [he,add_sub_cancel_left]

lemma lowJet_increment_position (G H : JetPolynomial.Base → JetPolynomial.Space) (x : JetPolynomial.Base) (i : Fin 2) :
    (lowJet (fun y => G y + H y) x - lowJet G x) (.inl i) = 0 := by
  change x i - x i = 0
  exact sub_self _

lemma weighted_increment_unscaled {U : Set JetPolynomial.Base} {W : JetPolynomial.Base → JetPolynomial.Space}
    {τ C : ℝ} {m : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    (hb : WeightedBound U τ m C W) :
    WeightedBound U 1 m (C / τ ^ m) W := by
  intro j hj x hx
  simp only [one_pow,one_mul]
  exact (hb.deriv_le hτ hj hx).trans (div_le_div_of_nonneg_left hC (pow_pos hτ _)
    (pow_le_pow_of_le_one hτ.le hτ1 hj))

lemma slow_increment_C3 {W : RealModes.RField 4} (hW : ContDiff ℝ ∞ W)
    {τ δ S : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    (hb : WeightedBound Set.univ τ 3 (S * δ * τ) W) :
    WeightedBound Set.univ 1 3 (S * δ / τ ^ 2) (W ∘ planeCoordinateIsometry) := by
  have hc := weightedBound_comp_isometry planeCoordinateIsometry hW hb
  have hh := weighted_increment_unscaled hτ hτ1
    (mul_nonneg (mul_nonneg hS hδ) hτ.le) hc
  convert hh using 1
  field_simp

lemma slow_increment_lowJet {G : JetPolynomial.Base → JetPolynomial.Space} {W : RealModes.RField 4}
    (hG : ContDiff ℝ ∞ G) (hW : ContDiff ℝ ∞ W)
    {τ δ S : ℝ} {m : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    (hb : WeightedBound Set.univ τ (m + 2) (S * δ * τ) W) :
    WeightedBound Set.univ τ m (S * δ / τ)
      (lowJet (fun x => G x + W (planeCoordinateIsometry x)) - lowJet G) := by
  have hc := weightedBound_comp_isometry planeCoordinateIsometry hW hb
  have hh := weighted_variationLowJet isOpen_univ
    (hW.comp planeCoordinateIsometry.contDiff) hτ hτ1
    (mul_nonneg (mul_nonneg hS hδ) hτ.le) m hc
  have hh' : WeightedBound Set.univ τ m (S * δ / τ)
      (variationLowJet (W ∘ planeCoordinateIsometry)) := by
    convert hh using 1
    field_simp
  apply hh'.congr
  intro x _
  exact congrFun (lowJet_increment_eq_variation hG
    (hW.comp planeCoordinateIsometry.contDiff)) x

lemma slow_increment_ratio {z : ℝ} (hz : 0 < z) (d b S : ℝ) :
    S * z ^ d / z ^ b = S * z ^ (d - b) := by
  rw [mul_div_assoc,← Real.rpow_sub hz]

lemma slow_increment_C3_ratio {z : ℝ} (hz : 0 < z) (d b S : ℝ) :
    S * z ^ d / (z ^ b) ^ (2 : ℕ) = S * z ^ (d - 2 * b) := by
  have he : (z ^ b) ^ (2 : ℕ) = z ^ (2 * b) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hz.le]
    congr 1
    ring
  rw [he,mul_div_assoc,← Real.rpow_sub hz]

/-- The actual update has small C3 displacement and small positional
two-jet at every fixed order.  The exponents are independent of the order. -/
theorem primitive_slow_increment_bounds {G : JetPolynomial.Base → JetPolynomial.Space} {W : RealModes.RField 4}
    (hG : ContDiff ℝ ∞ G) (hW : ContDiff ℝ ∞ W)
    {z d b : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) (hb : 0 ≤ b)
    (S : ℕ → ℝ) (hS : ∀ m, 0 ≤ S m)
    (hWb : ∀ m, WeightedBound Set.univ (z ^ b) m
      (S m * z ^ d * z ^ b) W) :
    WeightedBound Set.univ 1 3 (S 3 * z ^ (d - 2 * b))
      ((fun x => G x + W (planeCoordinateIsometry x)) - G) ∧
    (∀ m, WeightedBound Set.univ (z ^ b) m (S (m + 2) * z ^ (d - b))
      (lowJet (fun x => G x + W (planeCoordinateIsometry x)) - lowJet G)) := by
  have hτ : 0 < z ^ b := Real.rpow_pos_of_pos hz _
  have hτ1 : z ^ b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  have hδ : 0 ≤ z ^ d := Real.rpow_nonneg hz.le _
  constructor
  · have hh := slow_increment_C3 hW hτ hτ1 hδ (hS 3) (hWb 3)
    rw [slow_increment_C3_ratio hz] at hh
    apply hh.congr
    intro x _
    exact add_sub_cancel_left _ _
  · intro m
    have hh := slow_increment_lowJet hG hW hτ hτ1 hδ (hS (m + 2)) (hWb (m + 2))
    simpa only [slow_increment_ratio hz] using hh

lemma primitive_slow_increment_derivative {G : JetPolynomial.Base → JetPolynomial.Space} {W : RealModes.RField 4}
    (hG : ContDiff ℝ ∞ G) (hW : ContDiff ℝ ∞ W)
    {z d b : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) (hb : 0 ≤ b)
    (S : ℕ → ℝ) (hS : ∀ m, 0 ≤ S m)
    (hWb : ∀ m, WeightedBound Set.univ (z ^ b) m
      (S m * z ^ d * z ^ b) W) {j : ℕ} (hj : j ≤ 3) (x : JetPolynomial.Base) :
    ‖iteratedFDeriv ℝ j ((fun y => G y + W (planeCoordinateIsometry y)) - G) x‖ ≤
      S 3 * z ^ (d - 2 * b) := by
  have hh := (primitive_slow_increment_bounds hG hW hz hz1 hb S hS hWb).1
    j hj x (Set.mem_univ x)
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hh

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
