import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFrameEnvelope
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeBudgets
import OAI.Geometry.Immersion.ClosedSurface.RealBounds

namespace OAI

/-! Polynomial bounds for the actual normalized mean error and its
amplitude difference, with explicit finite derivative loss. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

theorem polynomial_normalizedMeanError (q m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {F : RField 4} {U : Set Base}, ContDiff ℝ ∞ F → RealModeDomain F U →
    ∀ {δ τ s B : ℝ}, 0 < δ → 0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 1 ≤ B →
      WeightedBound U s (m+q+2) B (realTwoJet F) →
      (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) →
      (∀ x ∈ U, ‖(realSecond F x ⬝ᵥ realSecond F x)⁻¹‖ ≤ B) →
    ∀ {b : Base → ℝ}, ContDiffOn ℝ ∞ b U → WeightedBound U s (m+q+2) B b →
    ∀ v w : Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound U s m (A*B^d*(τ/s)) (normalizedMeanError δ τ F b q v w) := by
  obtain ⟨p,C,hC,hframe⟩ := polynomial_frame_envelope (m+q+2)
  let K := fun x : ℝ => C*x^p
  have hK : HasPolynomialBound K :=
    (polynomialBound_const (zero_le_one.trans hC)).mul (polynomialBound_id.pow p)
  have hK1 (x : ℝ) (hx : 1 ≤ x) : 1 ≤ K x :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hx)
  have hpoly : HasPolynomialBound (fun x => meanErrorConstant 4 m (K x) q *
      (Real.sqrt 2 * 2^(m+q+2)*x*K x)^2) :=
    ((meanErrorConstant_polynomial 4 m q).comp hK hK1).mul
      (((((polynomialBound_const (by positivity)).mul (polynomialBound_const (by positivity))).mul
        polynomialBound_id).mul hK).pow 2)
  obtain ⟨d,A,hA,hpoly⟩ := hpoly
  refine ⟨d,A,hA,?_⟩
  intro F U hF hU δ τ s B hδ hτ hs hτs hs1 hB hjet hG hN b hb hbb v w hv hw
  obtain ⟨hcoeff,hfree⟩ := hframe hF hU hs hB hjet hG hN
  have hBK : 0 ≤ K B := zero_le_one.trans (hK1 B hB)
  have hh := weighted_normalizedMeanError hF hU hδ hτ hs hτs hs1 hBK
    (zero_le_one.trans hB) hBK hb q m hcoeff hbb hfree v w hv hw
  exact hh.mono_const (mul_le_mul_of_nonneg_right (hpoly B hB).2 (div_nonneg hτ.le hs.le))

theorem polynomial_normalizedMeanError_difference (q m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {F : RField 4} {U : Set Base}, ContDiff ℝ ∞ F → RealModeDomain F U →
    ∀ {δ τ s B D : ℝ}, 0 < δ → 0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 1 ≤ B → 0 ≤ D →
      WeightedBound U s (m+q+2) B (realTwoJet F) →
      (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) →
      (∀ x ∈ U, ‖(realSecond F x ⬝ᵥ realSecond F x)⁻¹‖ ≤ B) →
    ∀ {b c : Base → ℝ}, ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ c U →
      WeightedBound U s (m+q+2) B b → WeightedBound U s (m+q+2) B c →
      WeightedBound U s (m+q+2) D (b-c) →
    ∀ v w : Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound U s m (A*B^d*D*(τ/s))
        (fun x => normalizedMeanError δ τ F b q v w x - normalizedMeanError δ τ F c q v w x) := by
  obtain ⟨p,C,hC,hframe⟩ := polynomial_frame_envelope (m+q+2)
  let K := fun x : ℝ => C*x^p
  have hK : HasPolynomialBound K :=
    (polynomialBound_const (zero_le_one.trans hC)).mul (polynomialBound_id.pow p)
  have hK1 (x : ℝ) (hx : 1 ≤ x) : 1 ≤ K x :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hx)
  have hpoly : HasPolynomialBound (fun x => 2*meanErrorConstant 4 m (K x) q *
      (Real.sqrt 2 * 2^(m+q+2)*K x)^2*x) :=
    (((polynomialBound_const (by positivity)).mul
      ((meanErrorConstant_polynomial 4 m q).comp hK hK1)).mul
        ((((polynomialBound_const (by positivity)).mul (polynomialBound_const (by positivity))).mul
          hK).pow 2)).mul polynomialBound_id
  obtain ⟨d,A,hA,hpoly⟩ := hpoly
  refine ⟨d,A,hA,?_⟩
  intro F U hF hU δ τ s B D hδ hτ hs hτs hs1 hB hD hjet hG hN b c hb hc hbb hbc hdiff v w hv hw
  obtain ⟨hcoeff,hfree⟩ := hframe hF hU hs hB hjet hG hN
  have hBK : 0 ≤ K B := zero_le_one.trans (hK1 B hB)
  have hh := weighted_normalizedMeanError_difference hF hU hδ hτ hs hτs hs1 hBK
    (zero_le_one.trans hB) hD hBK hb hc q m hcoeff hbb hbc hdiff hfree v w hv hw
  exact hh.mono_const (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hpoly B hB).2 hD) (div_nonneg hτ.le hs.le))

end ClosedSurfaceR4.RealModes

end

end OAI
