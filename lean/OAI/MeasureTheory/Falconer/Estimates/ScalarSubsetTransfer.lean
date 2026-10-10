import OAI.MeasureTheory.Falconer.Estimates.ScalarSignedRuzsa

namespace OAI

/-! Transferring a small projection from an overlapping subset to its
reference set. Every denominator remains an actual covering number. -/
namespace Falconer
open scoped Pointwise

 theorem scalarCells_mono (δ : ℝ) {A B : Finset ℝ} (hAB : A ⊆ B) :
    scalarCells δ A ⊆ scalarCells δ B := Finset.image_subset_image hAB

 theorem scalar_subset_sum_transfer (δ : ℝ) (A B C D : Finset ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hBA : B ⊆ A)
    (h0 : ((scalarCells δ (A+D)).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+C)).card : ℝ) ≤ L) :
    ((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ B).card*(scalarCells δ D).card ≤ 64*L^3 := by
  have hBD : ((scalarCells δ (B+D)).card : ℝ) ≤ L :=
    (Nat.cast_le.mpr (Finset.card_le_card (scalarCells_mono δ
      (Finset.add_subset_add hBA (Finset.Subset.refl D))))).trans h0
  have hd : ((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ D).card ≤ 8*L^2 := by
    have hh : ((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ D).card ≤
        8*((scalarCells δ (B+D)).card : ℝ)*(scalarCells δ (A+D)).card := by
      exact_mod_cast scalar_ruzsa_triangle δ B D A
    have hprod := mul_le_mul hBD h0 (Nat.cast_nonneg _) hL
    nlinarith
  have hs : ((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ B).card ≤
      8*((scalarCells δ (B-A)).card : ℝ)*L := by
    have hh : ((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ B).card ≤
        8*((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ (B+C)).card := by
      exact_mod_cast scalar_ruzsa_sum_triangle δ A B C
    exact hh.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  calc
    _ ≤ (8*((scalarCells δ (B-A)).card : ℝ)*L)*(scalarCells δ D).card :=
      mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = (8*L)*(((scalarCells δ (B-A)).card : ℝ)*(scalarCells δ D).card) := by ring
    _ ≤ (8*L)*(8*L^2) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

 theorem scalar_subset_difference_transfer (δ : ℝ) (A B C D R : Finset ℝ)
    {L F : ℝ} (hL : 0 ≤ L) (hF : 0 ≤ F) (hBA : B ⊆ A)
    (h0 : ((scalarCells δ (A+D)).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+C)).card : ℝ) ≤ L)
    (hscale : ((scalarCells δ (R+C)).card : ℝ) ≤ F*L) :
    ((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ B).card*
      (scalarCells δ D).card*(scalarCells δ C).card ≤ 512*F*L^4 := by
  have hsum := scalar_subset_sum_transfer δ A B C D hL hBA h0 h1
  have hdiff : ((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ C).card ≤
      8*((scalarCells δ (A+C)).card : ℝ)*(F*L) := by
    have hh : ((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ C).card ≤
        8*((scalarCells δ (A+C)).card : ℝ)*(scalarCells δ (R+C)).card := by
      exact_mod_cast scalar_ruzsa_triangle δ A C R
    exact hh.trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  calc
    _ = (((scalarCells δ (A-R)).card : ℝ)*(scalarCells δ C).card)*
        ((scalarCells δ B).card*(scalarCells δ D).card) := by ring
    _ ≤ (8*((scalarCells δ (A+C)).card : ℝ)*(F*L))*
        ((scalarCells δ B).card*(scalarCells δ D).card) :=
      mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ = (8*F*L)*(((scalarCells δ (A+C)).card : ℝ)*
        (scalarCells δ B).card*(scalarCells δ D).card) := by ring
    _ ≤ (8*F*L)*(64*L^3) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Falconer

end OAI
