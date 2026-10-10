import OAI.MeasureTheory.Falconer.Geometry.ScalarCoverCount
import OAI.MeasureTheory.Falconer.Estimates.ScalarEnergyRefinement

namespace OAI

/-! Scalar dilation changes a fixed-resolution covering number by at
most a linear factor in the dilation bound. -/
namespace Falconer
open scoped Pointwise

theorem scalar_dilation_cells {δ c : ℝ} (hδ : 0 < δ) (A : Finset ℝ)
    (M : ℕ) (hc : |c| ≤ M) :
    (scalarCells δ (A.image fun x => c*x)).card ≤ (2*M+3)*(scalarCells δ A).card := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let g := Function.invFunOn q (A : Set ℝ)
  let F := (scalarCells δ A).image g
  have hF : F.card ≤ (scalarCells δ A).card := Finset.card_image_le
  have hcover : ∀ x ∈ A.image (fun x => c*x),
      ∃ y ∈ F.image (fun x => c*x), |x-y| ≤ (M : ℝ)*δ := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    have hq := Function.invFunOn_pos (f := q) (s := (A : Set ℝ)) ⟨x,hx,rfl⟩
    have hxg : |x-g (q x)| ≤ δ := (same_scalar_cell_dist_lt hδ hq.2.symm).le
    have hgf : g (q x) ∈ F := Finset.mem_image.mpr
      ⟨q x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩
    refine ⟨c*g (q x),Finset.mem_image.mpr ⟨g (q x),hgf,rfl⟩,?_⟩
    rw [← mul_sub,abs_mul]
    exact mul_le_mul hc hxg (abs_nonneg _) (Nat.cast_nonneg M)
  have hn := scalarCells_near_card_nat hδ (A.image fun x => c*x) (F.image fun x => c*x) M hcover
  have hsmall : (scalarCells δ (F.image fun x => c*x)).card ≤ (scalarCells δ A).card :=
    Finset.card_image_le.trans (Finset.card_image_le.trans hF)
  exact hn.trans (Nat.mul_le_mul_left _ hsmall)

theorem scalar_inverse_coefficient_cells {δ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (X : Finset ℝ) (M : ℕ) (hM : |a⁻¹| ≤ M) :
    (scalarCells δ (X+X.image (fun x => a⁻¹*x))).card ≤
      (2*M+3)*(scalarCells δ (X+X.image (fun x => a*x))).card := by
  classical
  have he : X+X.image (fun x => a⁻¹*x) =
      (X+X.image (fun x => a*x)).image (fun x => a⁻¹*x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨y+a*x,Finset.add_mem_add hy
        (Finset.mem_image.mpr ⟨x,hx,rfl⟩),?_⟩
      simp only [mul_add,← mul_assoc,inv_mul_cancel₀ ha,one_mul,add_comm]
    · intro hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨x,hx,w,hw,rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have heq : a⁻¹*(x+a*y) = y+a⁻¹*x := by
        simp only [mul_add,← mul_assoc,inv_mul_cancel₀ ha,one_mul,add_comm]
      rw [heq]
      exact Finset.add_mem_add hy (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  rw [he]
  exact scalar_dilation_cells hδ _ M hM

end Falconer

end OAI
