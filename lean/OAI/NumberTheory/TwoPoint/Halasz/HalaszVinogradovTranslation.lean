import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal

namespace OAI

/-! Translation and dilation preserve the complete Vinogradov system.
These are the finite identities used before averaging its solutions. -/
namespace TwoPointCorrelations

open Finset

theorem halasz_vinogradov_translate {s k : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i^j = ∑ i, y i^j)
    (c : ℚ) : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i, (x i+c)^j = ∑ i, (y i+c)^j := by
  intro j _hj hjk
  have hbinom (z : Fin s → ℚ) :
      (∑ i, (z i+c)^j) = ∑ m ∈ range (j+1),
        (∑ i, z i^m)*c^(j-m)*(Nat.choose j m:ℚ) := by
    simp only [add_pow]
    rw [sum_comm]
    apply sum_congr rfl
    intro m _
    rw [← sum_mul,← sum_mul]
  rw [hbinom,hbinom]
  apply sum_congr rfl
  intro m hm
  have hmj : m ≤ j := by have := mem_range.mp hm; omega
  have he : (∑ i, x i^m) = ∑ i, y i^m := by
    by_cases hz : m=0
    · simp [hz]
    · exact hpower m (by omega) (hmj.trans hjk)
  rw [he]

theorem halasz_vinogradov_dilate {s k : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i^j = ∑ i, y i^j)
    (a : ℚ) : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i, (a*x i)^j = ∑ i, (a*y i)^j := by
  intro j hj hjk
  simp only [mul_pow,← mul_sum]
  rw [hpower j hj hjk]

theorem halasz_vinogradov_affine {s k : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i^j = ∑ i, y i^j)
    (a c : ℚ) : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i, (a*x i+c)^j = ∑ i, (a*y i+c)^j :=
  halasz_vinogradov_translate _ _ (halasz_vinogradov_dilate x y hpower a) c

end TwoPointCorrelations

end OAI
