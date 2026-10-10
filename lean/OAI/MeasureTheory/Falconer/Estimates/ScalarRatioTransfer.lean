import OAI.MeasureTheory.Falconer.Estimates.ScalarSubsetTransfer
import OAI.MeasureTheory.Falconer.Estimates.ScalarDilationBound

namespace OAI

/-! Two overlapping small projections give a small difference projection
for the ratio of their coefficients. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_dilation_sum_image (A Y : Finset ℝ) {a b r : ℝ} (h : r*a = b) :
    A.image (fun x => r*x)+Y.image (fun y => b*y) =
      (A+Y.image (fun y => a*y)).image (fun x => r*x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨x+a*y,Finset.add_mem_add hx
      (Finset.mem_image.mpr ⟨y,hy,rfl⟩),?_⟩
    rw [mul_add,← mul_assoc,h]
  · intro hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    rw [mul_add,← mul_assoc,h]
    exact Finset.add_mem_add (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      (Finset.mem_image.mpr ⟨y,hy,rfl⟩)

 theorem scalar_ratio_transfer {δ a b r L : ℝ} (hδ : 0 < δ)
    (hL : 0 ≤ L) (A B Y : Finset ℝ) (hBA : B ⊆ A)
    (hr : r*a = b) (M : ℕ) (hM : |r| ≤ M)
    (h0 : ((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) ≤ L)
    (h1 : ((scalarCells δ (B+Y.image (fun y => b*y))).card : ℝ) ≤ L) :
    ((scalarCells δ (A-A.image (fun x => r*x))).card : ℝ)*
      (scalarCells δ B).card*(scalarCells δ (Y.image (fun y => a*y))).card*
      (scalarCells δ (Y.image (fun y => b*y))).card ≤ 512*(2*M+3)*L^4 := by
  have hs : ((scalarCells δ (A.image (fun x => r*x)+Y.image (fun y => b*y))).card : ℝ) ≤
      (2*M+3)*L := by
    rw [scalar_dilation_sum_image A Y hr]
    have hh : ((scalarCells δ ((A+Y.image (fun y => a*y)).image (fun x => r*x))).card : ℝ) ≤
        (2*M+3)*((scalarCells δ (A+Y.image (fun y => a*y))).card : ℝ) := by
      exact_mod_cast scalar_dilation_cells hδ (A+Y.image (fun y => a*y)) M hM
    exact hh.trans (mul_le_mul_of_nonneg_left h0 (by positivity))
  exact scalar_subset_difference_transfer δ A B (Y.image fun y => b*y)
    (Y.image fun y => a*y) (A.image fun x => r*x) hL (by positivity) hBA h0 h1 hs

end Falconer

end OAI
