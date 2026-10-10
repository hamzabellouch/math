import OAI.MeasureTheory.Falconer.Estimates.ScalarCollisionKernel

namespace OAI

/-! Comparing small scalar projections with the collision kernel of
the original finite Cartesian product. -/
namespace Falconer
open scoped Pointwise

theorem scalarPairCell_image_product (δ c : ℝ) (X Y : Finset ℝ) :
    (X ×ˢ Y).image (scalarPairCell δ c) = scalarCells δ (X+Y.image (fun y => c*y)) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨⟨x,y⟩,hp,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_image.mpr ⟨x+c*y,Finset.add_mem_add hx
      (Finset.mem_image.mpr ⟨y,hy,rfl⟩),rfl⟩
  · intro hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩

theorem scalar_projection_energy_lower (δ : ℝ) (A : Finset ℝ) (S : Finset (ℝ × ℝ))
    {M : ℝ} (hproj : ∀ c ∈ A, ((S.image (scalarPairCell δ c)).card : ℝ) ≤ M) :
    (A.card : ℝ)*(S.card : ℝ)^2 ≤
      M*∑ c ∈ A, ((cellCollisions S (scalarPairCell δ c)).card : ℝ) := by
  calc
    _ = ∑ _c ∈ A, (S.card : ℝ)^2 := by simp
    _ ≤ ∑ c ∈ A, M*((cellCollisions S (scalarPairCell δ c)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      exact (finite_cell_energy_lower S (scalarPairCell δ c)).trans
        (mul_le_mul_of_nonneg_right (hproj c hc) (Nat.cast_nonneg _))
    _ = _ := by rw [Finset.mul_sum]

theorem scalar_product_projection_comparison {δ η R M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hM : 0 ≤ M)
    (A X Y : Finset ℝ) (hA : ∀ c ∈ A, |c| ≤ R)
    (hsepA : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|)
    (hsepX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hproj : ∀ c ∈ A, ((scalarCells δ (X+Y.image (fun y => c*y))).card : ℝ) ≤ M) :
    (A.card : ℝ)*((X.card : ℝ)*(Y.card : ℝ))^2 ≤
      M*((A.card : ℝ)*(X.card : ℝ)*(Y.card : ℝ)+
        ∑ p ∈ X ×ˢ Y, ∑ q ∈ X ×ˢ Y, scalarCollisionKernel δ η R p q) := by
  have hrow : ∀ p ∈ X ×ˢ Y, ∀ q ∈ X ×ˢ Y,
      p.2 = q.2 → p ≠ q → δ ≤ |p.1-q.1| := by
    intro p hp q hq he hne
    apply hsepX _ (Finset.mem_product.mp hp).1 _ (Finset.mem_product.mp hq).1
    intro hfirst
    exact hne (Prod.ext hfirst he)
  have hlow := scalar_projection_energy_lower δ A (X ×ˢ Y) (fun c hc => by
    rw [scalarPairCell_image_product]
    exact hproj c hc)
  have hhigh := scalar_projection_kernel_sum hδ hη A hA hsepA (X ×ˢ Y) hrow
  have hh := hlow.trans (mul_le_mul_of_nonneg_left hhigh hM)
  simpa only [Finset.card_product,Nat.cast_mul,mul_assoc] using hh

end Falconer

end OAI
