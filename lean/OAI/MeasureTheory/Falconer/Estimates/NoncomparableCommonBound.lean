import OAI.MeasureTheory.Falconer.Estimates.NoncomparableOriginalPointwise

namespace OAI

/-! # A common normalization for both original noncomparable factors -/

namespace Falconer

theorem noncomparable_coefficient_common {H W S M c₁ c₂ u v : ℝ}
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h₁u : c₁ ≤ u) (h₂u : c₂ ≤ u) :
    H*c₁*c₂*M*v+4*W*S*c₁*(2*(max c₁ c₂*M)+S*c₁) ≤
      (H*M*v+4*W*S*(2*M+S))*u^2 := by
  have hm := max_le h₁u h₂u
  calc
    _ ≤ H*u*u*M*v+4*W*S*u*(2*(u*M)+S*u) := by gcongr
    _ = _ := by ring

 theorem normalized_jet_bound_mono {B C A : ℝ} (hB : 0 ≤ B) (hBC : B ≤ C)
    (hA : 0 < A) (K p : ℕ) : (B^K*A⁻¹)^p ≤ (C^K*A⁻¹)^p :=
  pow_le_pow_left₀ (mul_nonneg (pow_nonneg hB _) (inv_nonneg.mpr hA.le))
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hBC K) (inv_nonneg.mpr hA.le)) p

end Falconer

end OAI
