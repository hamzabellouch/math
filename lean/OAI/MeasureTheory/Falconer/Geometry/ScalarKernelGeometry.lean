import OAI.MeasureTheory.Falconer.Estimates.ScalarCollisionKernel
import OAI.MeasureTheory.Falconer.Measures.ScalarProductBalls

namespace OAI

/-! Relating the scalar collision kernel to the Euclidean potential
of the original Cartesian product. -/
namespace Falconer

theorem rowPoint_pair_dist_lower (p q : ℝ × ℝ) :
    |p.2-q.2| ≤ dist (rowPoint p.1 p.2) (rowPoint q.1 q.2) := by
  simpa only [rowPoint_one,Real.dist_eq] using
    PiLp.dist_apply_le (rowPoint p.1 p.2) (rowPoint q.1 q.2) 1

theorem rowPoint_pair_dist_upper {δ : ℝ} (p q : ℝ × ℝ)
    (hδ : δ ≤ |p.2-q.2|) (hs : |p.1-q.1| ≤ δ+|p.2-q.2|) :
    dist (rowPoint p.1 p.2) (rowPoint q.1 q.2) ≤ 3*|p.2-q.2| := by
  have he := EuclideanSpace.dist_sq_eq (rowPoint p.1 p.2) (rowPoint q.1 q.2)
  simp only [Fin.sum_univ_two,rowPoint_zero,rowPoint_one,Real.dist_eq,sq_abs] at he
  have hxy : |p.1-q.1| ≤ 2*|p.2-q.2| := by linarith
  have hx2 := mul_le_mul hxy hxy (abs_nonneg _) (by positivity)
  nlinarith [dist_nonneg (x := rowPoint p.1 p.2) (y := rowPoint q.1 q.2),
    abs_nonneg (p.2-q.2),sq_abs (p.1-q.1),sq_abs (p.2-q.2)]

theorem scalar_kernel_le_euclidean {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (p q : ℝ × ℝ) (hsep : p.2 ≠ q.2 → δ ≤ |p.2-q.2|) :
    scalarCollisionKernel δ η 1 p q ≤
      5+12*(δ/η)*(1/max (dist (rowPoint p.1 p.2) (rowPoint q.1 q.2)) δ) := by
  classical
  have hnonneg : 0 ≤ 12*(δ/η)*(1/max (dist (rowPoint p.1 p.2) (rowPoint q.1 q.2)) δ) := by
    positivity
  by_cases hy : p.2 = q.2
  · rw [scalarCollisionKernel,ite_eq_left hy]
    linarith
  by_cases hs : |p.1-q.1| ≤ δ+1*|p.2-q.2|
  · have hdy := hsep hy
    have hypos : 0 < |p.2-q.2| := hδ.trans_le hdy
    have hd := rowPoint_pair_dist_lower p q
    have hdpos := hypos.trans_le hd
    have hdδ : δ ≤ dist (rowPoint p.1 p.2) (rowPoint q.1 q.2) := hdy.trans hd
    have hupper := rowPoint_pair_dist_upper p q hdy (by simpa only [one_mul] using hs)
    have hinv : 1/|p.2-q.2| ≤ 3/dist (rowPoint p.1 p.2) (rowPoint q.1 q.2) := by
      apply (div_le_div_iff₀ hypos hdpos).2
      simpa only [one_mul] using hupper
    have hm := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4*(δ/η) by positivity)
    rw [scalarCollisionKernel,ite_eq_right hy,ite_eq_left hs,max_eq_left hdδ]
    have he1 : 4*δ/(η*|p.2-q.2|) = (4*(δ/η))*(1/|p.2-q.2|) := by ring
    have he2 : 12*(δ/η)*(1/dist (rowPoint p.1 p.2) (rowPoint q.1 q.2)) =
        (4*(δ/η))*(3/dist (rowPoint p.1 p.2) (rowPoint q.1 q.2)) := by ring
    rw [he1,he2]
    exact add_le_add le_rfl hm
  · simp only [scalarCollisionKernel,hy,hs,ite_false]
    linarith

theorem scalar_kernel_sum_le_potential {δ η V : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (X Y : Finset ℝ) (hsep : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → δ ≤ |y-z|)
    (hpot : ∀ z ∈ scalarProductPoints X Y,
      (∑ q ∈ scalarProductPoints X Y, 1/max (dist z q) δ) ≤ V) :
    (∑ p ∈ X ×ˢ Y, ∑ q ∈ X ×ˢ Y, scalarCollisionKernel δ η 1 p q) ≤
      5*((X.card : ℝ)*(Y.card : ℝ))^2+12*(δ/η)*((X.card : ℝ)*(Y.card : ℝ))*V := by
  classical
  have hinner (p : ℝ × ℝ) (hp : p ∈ X ×ˢ Y) :
      (∑ q ∈ X ×ˢ Y, scalarCollisionKernel δ η 1 p q) ≤
        5*((X.card : ℝ)*(Y.card : ℝ))+12*(δ/η)*V := by
    have hb := hpot (rowPoint p.1 p.2) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    rw [scalarProductPoints,Finset.sum_image (fun _ _ _ _ h => rowPoint_pair_injective h)] at hb
    calc
      _ ≤ ∑ q ∈ X ×ˢ Y, (5+12*(δ/η)*(1/max
          (dist (rowPoint p.1 p.2) (rowPoint q.1 q.2)) δ)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact scalar_kernel_le_euclidean hδ hη p q
          (fun hne => hsep _ (Finset.mem_product.mp hp).2 _ (Finset.mem_product.mp hq).2 hne)
      _ = 5*((X.card : ℝ)*(Y.card : ℝ))+12*(δ/η)*
          ∑ q ∈ X ×ˢ Y, 1/max (dist (rowPoint p.1 p.2) (rowPoint q.1 q.2)) δ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        simp [Finset.card_product,Nat.cast_mul,mul_comm]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by positivity))
  calc
    _ ≤ ∑ _p ∈ X ×ˢ Y, (5*((X.card : ℝ)*(Y.card : ℝ))+12*(δ/η)*V) :=
      Finset.sum_le_sum hinner
    _ = _ := by simp [Finset.card_product,Nat.cast_mul]; ring

end Falconer

end OAI
