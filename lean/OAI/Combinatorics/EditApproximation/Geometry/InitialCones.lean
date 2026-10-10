import OAI.Combinatorics.EditApproximation.Geometry.StateGeometry
import OAI.Combinatorics.EditApproximation.Numerics.RationalRefinement
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Rational scaled seeds and the actual cone lower invariant

Ceilings preserve the upper bound because `F*c` is an integer. Cone lower
bounds use the actual edit-distance and signed-length geometry, rather
than an assumed lower-bound-preserving cone oracle.
-/

namespace EditApproximation



theorem rationalStateGap_cast {α : Type*} (source target : List α)
    (q : TargetInterval target.length) :
    (rationalStateGap source target q : ℝ) = stateLengthGap source target q := by
  simp only [rationalStateGap, stateLengthGap, Rat.cast_sub, Rat.cast_natCast]



theorem scaledSeedValue_bounds (U c F : ℕ) (a gap : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F) (hU : c ≤ U)
    (hupper : (U : ℚ) ≤ a * F * c) (hgap : |gap| ≤ c) :
    max ((c : ℚ) / a) |gap| ≤ scaledSeedValue U a gap ∧ scaledSeedValue U a gap ≤ F * c := by
  have ha0 : 0 < a := by linarith
  have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
  have hc0 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  have hratio : (U : ℚ) / a ≤ F * c := by
    apply (div_le_iff₀ ha0).2
    nlinarith
  have hceil : ⌈(U : ℚ) / a⌉₊ ≤ F * c := Nat.ceil_le.mpr (by exact_mod_cast hratio)
  constructor
  · apply max_le_max _ le_rfl
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hU) ha0.le).trans (Nat.le_ceil _)
  · apply max_le (by exact_mod_cast hceil) _
    exact hgap.trans (by nlinarith)

theorem scaledSeedValue_zero (a : ℚ) : scaledSeedValue 0 a 0 = 0 := by
  simp only [scaledSeedValue, Nat.cast_zero, zero_div, Nat.ceil_zero, abs_zero, max_self]



theorem initialConeValue_actual_lower {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (a L0 : ℚ)
    (query center : TargetInterval target.length) (ha : 1 ≤ a) (hL : 1 ≤ L0)
    (hseed : stateEditCost source target center ≤ U center) :
    max ((stateEditCost source target query : ℚ) / a) |rationalStateGap source target query| ≤
      initialConeValue source target U a L0 query center := by
  have ha0 : 0 < a := by linarith
  let distance : ℚ := targetEndpointDistance query center
  let base := scaledSeedValue (U center) a (rationalStateGap source target center)
  have hd0 : 0 ≤ distance := Nat.cast_nonneg _
  have hbaseCost : (stateEditCost source target center : ℚ) / a ≤ base :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hseed) ha0.le).trans
      ((Nat.le_ceil _).trans (le_max_left _ _))
  have hbaseGap : |rationalStateGap source target center| ≤ base := le_max_right _ _
  have hdistDiv : distance / a ≤ distance := by
    apply (div_le_iff₀ ha0).2
    nlinarith
  have hdistSlope : distance ≤ L0 * distance := by nlinarith
  have hcost : (stateEditCost source target query : ℚ) ≤ stateEditCost source target center + distance := by
    dsimp only [distance]
    exact_mod_cast stateEditCost_spatial source target query center
  have hgap : |rationalStateGap source target query| ≤ |rationalStateGap source target center| + distance := by
    have h := stateLengthGap_spatial source target query center
    rw [← rationalStateGap_cast, ← rationalStateGap_cast] at h
    exact_mod_cast h
  change max ((stateEditCost source target query : ℚ) / a) |rationalStateGap source target query| ≤
    base + L0 * distance
  apply max_le
  · have hdivide := div_le_div_of_nonneg_right hcost ha0.le
    rw [add_div] at hdivide
    linarith
  · linarith

end EditApproximation

end OAI
