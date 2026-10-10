import OAI.MeasureTheory.Falconer.Estimates.ScalarScaledCard
import OAI.MeasureTheory.Falconer.Estimates.ScalarDifferenceDoubling

namespace OAI

/-! A small nondegenerate projection gives doubling of its first factor. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_difference_from_sum {δ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (A Y : Finset ℝ) (M : ℕ) (haM : |a⁻¹| ≤ M)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) :
    ((scalarCells δ (A-A)).card : ℝ)*(Y.card : ℝ) ≤
      8*(2*M+3)*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ)^2 := by
  have hlower := scalar_scaled_cells_lower hδ ha Y M haM hYsep
  have ht : ((scalarCells δ (A-A)).card : ℝ)*
      (scalarCells δ (Y.image (fun y => a*y))).card ≤
      8*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ)^2 := by
    have hh := scalar_ruzsa_triangle δ A (Y.image fun y => a*y) A
    exact_mod_cast (by simpa only [pow_two,mul_assoc] using hh)
  calc
    _ ≤ ((scalarCells δ (A-A)).card : ℝ)*
        ((2*M+3)*((scalarCells δ (Y.image (fun y => a*y))).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg _)
    _ = (2*M+3 : ℝ)*(((scalarCells δ (A-A)).card : ℝ)*
        (scalarCells δ (Y.image (fun y => a*y))).card) := by ring
    _ ≤ (2*M+3 : ℝ)*(8*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ)^2) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

 theorem scalar_doubling_from_projection {δ a K ρ : ℝ} (hδ : 0 < δ)
    (ha : a ≠ 0) (hρ : 0 < ρ)
    (A Y : Finset ℝ) (hA : A.Nonempty) (M : ℕ) (haM : |a⁻¹| ≤ M)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hYsize : ρ*((scalarCells δ A).card : ℝ) ≤ (Y.card : ℝ))
    (hsmall : ((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) ≤
      K*(scalarCells δ A).card) :
    ((scalarCells δ (A+A)).card : ℝ) ≤
      (1024*(2*M+3)^2*K^4/ρ^2)*(scalarCells δ A).card := by
  have hAc : 0 < ((scalarCells δ A).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.image_nonempty.mpr hA))
  have hd := scalar_difference_from_sum hδ ha A Y M haM hYsep
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hsmall 2
  have hbound : ((scalarCells δ (A-A)).card : ℝ)*(ρ*(scalarCells δ A).card) ≤
      8*(2*M+3)*(K*((scalarCells δ A).card : ℝ))^2 := by
    calc
      _ ≤ ((scalarCells δ (A-A)).card : ℝ)*(Y.card : ℝ) :=
        mul_le_mul_of_nonneg_left hYsize (Nat.cast_nonneg _)
      _ ≤ _ := hd.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hdiff : ((scalarCells δ (A-A)).card : ℝ) ≤
      (8*(2*M+3)*K^2/ρ)*(scalarCells δ A).card := by
    calc
      _ ≤ (8*(2*M+3)*(K*((scalarCells δ A).card : ℝ))^2)/
          (ρ*(scalarCells δ A).card) := (le_div_iff₀ (mul_pos hρ hAc)).2 hbound
      _ = _ := by field_simp
  have hh := scalar_doubling_of_difference δ A hA hdiff
  convert hh using 1
  ring

end Falconer

end OAI
