import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientAdd

namespace OAI

/-! Negating a coefficient with a small sumset, by the scalar Ruzsa
triangle inequality. -/
namespace Falconer
open scoped Pointwise

theorem scalar_coefficient_neg (δ a : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (-a)*x))).card : ℝ) ≤
      8*K^2*(scalarCells δ X).card := by
  classical
  have he : X+X.image (fun x => (-a)*x) = X-X.image (fun x => a*x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_sub.mpr ⟨x,hx,a*y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,by ring⟩
    · intro hz
      obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_add.mpr ⟨x,hx,(-a)*y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,by ring⟩
  rw [he]
  have hR := scalar_ruzsa_triangle δ X X (X.image fun x => a*x)
  have hRR : ((scalarCells δ (X-X.image (fun x => a*x))).card : ℝ)*(scalarCells δ X).card ≤
      8*((scalarCells δ (X+X)).card : ℝ)*(scalarCells δ (X.image (fun x => a*x)+X)).card := by
    exact_mod_cast hR
  have ha' : ((scalarCells δ (X.image (fun x => a*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact ha
  have hprod := mul_le_mul hdoubling ha' (Nat.cast_nonneg _) (mul_nonneg hK (Nat.cast_nonneg _))
  have hAc : 0 < ((scalarCells δ X).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.image_nonempty.mpr hX))
  apply (mul_le_mul_iff_right₀ hAc).1
  nlinarith

end Falconer

end OAI
