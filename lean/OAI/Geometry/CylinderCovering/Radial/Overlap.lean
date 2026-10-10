import OAI.Geometry.CylinderCovering.Radial.OverlapDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialOverlap

theorem overlap_identities : IdentitiesStatement := by
  intro ε x y t p q h
  obtain ⟨hq, hp⟩ := h
  dsimp [rho, sigma, T, S, RadialCaps.G]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination ε * q * hp - ε * p * hq
  · linear_combination ε * x * hq
  · linear_combination -ε * y * hp
  · linear_combination -2 * ε * x * hq
  · linear_combination 2 * ε * y * hp

private theorem product_abs_le {x q : ℝ} (hx : |x| ≤ 2) (hq : |q| ≤ 1) :
    |x * q| ≤ 2 := by
  rw [abs_mul]
  nlinarith [abs_nonneg x, abs_nonneg q]

private theorem weighted_square_le {x q : ℝ} (hx : |x| ≤ 2) (hq : |q| ≤ 1) :
    x ^ 2 * RadialCaps.G q ≤ 4 := by
  have hx2 : x ^ 2 ≤ 4 := by nlinarith [sq_abs x, abs_nonneg x]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [sq_abs q, abs_nonneg q]
  have hG0 : 0 ≤ RadialCaps.G q := by unfold RadialCaps.G; positivity
  have hG1 : RadialCaps.G q ≤ 1 := by unfold RadialCaps.G; linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hx2) hG0]

theorem complementary_bound : ComplementaryBoundStatement := by
  intro ε x y t p q hε hsmall hx hy hp hq hroot hT hS
  obtain ⟨_, hTi, hSi, _, _⟩ := overlap_identities ε x y t p q hroot
  have hxq := product_abs_le hx hq
  have hyp := product_abs_le hy hp
  have hcT : 1 / 2 ≤ 1 + ε * x * q := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hxq).1 hε.le
    nlinarith
  have hcS : 1 / 2 ≤ 1 - ε * y * p := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hyp).2 hε.le
    nlinarith
  have hw : x ^ 2 * RadialCaps.G q + y ^ 2 * RadialCaps.G p ≤ 8 := by
    linarith [weighted_square_le hx hq, weighted_square_le hy hp]
  have hsum : -8 * ε ^ 2 ≤
      (1 + ε * x * q) * T ε x t q + (1 - ε * y * p) * S ε y t p := by
    rw [hTi, hSi]
    have hh := mul_le_mul_of_nonneg_left hw (sq_nonneg ε)
    nlinarith only [hh]
  have hT0 : (1 + ε * x * q) * T ε x t q ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hT
  have hS0 : (1 - ε * y * p) * S ε y t p ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hS
  have hTa := mul_le_mul_of_nonpos_right hcT hT
  have hSa := mul_le_mul_of_nonpos_right hcS hS
  rw [abs_of_nonpos hT, abs_of_nonpos hS]
  constructor <;> nlinarith only [hsum, hT0, hS0, hTa, hSa]

theorem monotonicity_defect (p q : ℝ) :
    (p ^ 2 - q ^ 2) * (RadialCaps.G p - RadialCaps.G q) =
      (p ^ 2 - q ^ 2) ^ 2 / 2 := by
  unfold RadialCaps.G
  ring

theorem physical_complementary_bound {k τ A B : ℝ} (hk : 0 < k)
    (hA : |A| ≤ 16 * (k * τ) ^ 2) (hB : |B| ≤ 16 * (k * τ) ^ 2) :
    |A / k| ≤ 16 * k * τ ^ 2 ∧ |B / k| ≤ 16 * k * τ ^ 2 := by
  rw [abs_div, abs_div, abs_of_pos hk]
  constructor
  · apply (div_le_iff₀ hk).2
    nlinarith only [hA]
  · apply (div_le_iff₀ hk).2
    nlinarith only [hB]

end CylinderCovering.RadialOverlap

end

end OAI
