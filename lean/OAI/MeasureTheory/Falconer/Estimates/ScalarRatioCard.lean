import OAI.MeasureTheory.Falconer.Estimates.ScalarRatioTransfer
import OAI.MeasureTheory.Falconer.Estimates.ScalarScaledCard

namespace OAI

/-! Ratio projection transfer expressed in cardinalities of the actual
separated overlap sets. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_ratio_card_bound {δ a b r L : ℝ} (hδ : 0 < δ)
    (hL : 0 ≤ L) (ha : a ≠ 0) (hb : b ≠ 0)
    (A B Y : Finset ℝ) (hBA : B ⊆ A)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (hr : r*a = b) (M R : ℕ) (haM : |a⁻¹| ≤ M) (hbM : |b⁻¹| ≤ M) (hrR : |r| ≤ R)
    (h0 : ((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+Y.image (fun y => b*y))).card : ℝ) ≤ L) :
    ((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*
      (B.card : ℝ)*(Y.card : ℝ)^2 ≤ 512*(2*R+3)*(2*M+3)^2*L^4 := by
  have hpre := scalar_ratio_transfer hδ hL A B Y hBA hr R hrR h0 h1
  have hBc : (scalarCells δ B).card = B.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hBsep)
  rw [hBc] at hpre
  have hYa := scalar_scaled_cells_lower hδ ha Y M haM hYsep
  have hYb := scalar_scaled_cells_lower hδ hb Y M hbM hYsep
  have hYs : (Y.card : ℝ)^2 ≤ ((2*M+3 : ℝ)^2)*
      (scalarCells δ (Y.image (fun y => a*y))).card*
      (scalarCells δ (Y.image (fun y => b*y))).card := by
    have hh := mul_le_mul hYa hYb (Nat.cast_nonneg _) (by positivity)
    convert hh using 1 <;> ring
  calc
    _ ≤ (((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*(B.card : ℝ))*
        (((2*M+3 : ℝ)^2)*(scalarCells δ (Y.image (fun y => a*y))).card*
          (scalarCells δ (Y.image (fun y => b*y))).card) :=
      mul_le_mul_of_nonneg_left hYs (by positivity)
    _ = (2*M+3 : ℝ)^2*(((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*
        (B.card : ℝ)*(scalarCells δ (Y.image (fun y => a*y))).card*
          (scalarCells δ (Y.image (fun y => b*y))).card) := by ring
    _ ≤ (2*M+3 : ℝ)^2*(512*(2*R+3)*L^4) :=
      mul_le_mul_of_nonneg_left hpre (by positivity)
    _ = _ := by ring

 theorem scalar_ratio_card_lower {D ρ N V B Y L : ℝ}
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hV : 0 ≤ V)
    (hB : ρ^4*N/2 ≤ B) (hY : ρ^4*V/2 ≤ Y)
    (hpre : D*B*Y^2 ≤ L) : D*ρ^12*N*V^2 ≤ 8*L := by
  have hYsq : (ρ^4*V/2)^2 ≤ Y^2 := pow_le_pow_left₀ (by positivity) hY 2
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ ρ^4*N/2).trans hB
  have hprod := mul_le_mul hB hYsq (by positivity) hB0
  have hd := mul_le_mul_of_nonneg_left hprod hD
  calc
    _ = 8*(D*((ρ^4*N/2)*(ρ^4*V/2)^2)) := by ring
    _ ≤ 8*(D*(B*Y^2)) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = 8*(D*B*Y^2) := by ring
    _ ≤ 8*L := mul_le_mul_of_nonneg_left hpre (by norm_num)

end Falconer

end OAI
