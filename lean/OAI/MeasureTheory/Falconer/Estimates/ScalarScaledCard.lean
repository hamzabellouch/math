import OAI.MeasureTheory.Falconer.Estimates.ScalarDilationBound

namespace OAI

/-! Lower bounds for covering numbers of scalar dilates, using only
the inverse dilation required by the projection application. -/
namespace Falconer

 theorem scalarCells_dilate_inverse {a : ℝ} (ha : a ≠ 0) (Y : Finset ℝ) :
    (Y.image fun y => a*y).image (fun y => a⁻¹*y) = Y := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hu
    simpa only [← mul_assoc,inv_mul_cancel₀ ha,one_mul] using hy
  · intro hz
    refine Finset.mem_image.mpr ⟨a*z,Finset.mem_image.mpr ⟨z,hz,rfl⟩,?_⟩
    rw [← mul_assoc,inv_mul_cancel₀ ha,one_mul]

 theorem scalar_scaled_cells_lower {δ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (Y : Finset ℝ) (M : ℕ) (hM : |a⁻¹| ≤ M)
    (hsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) :
    (Y.card : ℝ) ≤ (2*M+3)*((scalarCells δ (Y.image (fun y => a*y))).card : ℝ) := by
  have hh := scalar_dilation_cells hδ (Y.image fun y => a*y) M hM
  rw [scalarCells_dilate_inverse ha Y] at hh
  have hcard : (scalarCells δ Y).card = Y.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
  rw [hcard] at hh
  exact_mod_cast hh

end Falconer

end OAI
