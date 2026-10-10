import OAI.MeasureTheory.Falconer.Measures.ScalarProductBalls

namespace OAI

/-! Actual graph edges in a narrow Cartesian strip are covered by planar
balls. The count retains every neighbor, rather than only one witness. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rowPoint_dist_le_sum {x y z w R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : |x-z| ≤ R) (hy : |y-w| ≤ S) :
    dist (rowPoint x y) (rowPoint z w) ≤ R+S := by
  have he := EuclideanSpace.dist_sq_eq (rowPoint x y) (rowPoint z w)
  simp only [Fin.sum_univ_two,rowPoint_zero,rowPoint_one,Real.dist_eq,sq_abs] at he
  have hx2 := mul_le_mul hx hx (abs_nonneg _) hR
  have hy2 := mul_le_mul hy hy (abs_nonneg _) hS
  nlinarith [sq_abs (x-z),sq_abs (y-w),mul_nonneg hR hS,
    dist_nonneg (x := rowPoint x y) (y := rowPoint z w)]

 theorem normalized_ball_bound_all_radii {δ t K : ℝ} {G : Finset (Space 2)}
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hG : NormalizedFiniteBallBound δ t K G)
    (z : Space 2) (r : ℝ) (hr : δ ≤ r) :
    ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ K*r^t*(G.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hG z r hr hr1
  · have hrpos : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hp : 1 ≤ r^t := Real.one_le_rpow hrpos ht
    have hc : ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ (G.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hk : 1 ≤ K*r^t := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) G.card])

 theorem scalar_graph_ball_cover {δ t K R S z : ℝ}
    (F Y Q : Finset ℝ) (e : ℝ → ℝ → Prop) (G : Finset (Space 2))
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hδ : δ ≤ R+S)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hreg : NormalizedFiniteBallBound δ t K G)
    (hF : ∀ x ∈ F, |x-z| ≤ R)
    (hcover : ∀ y ∈ Y, ∃ q ∈ Q, |y-q| ≤ S)
    (hgraph : ∀ x ∈ F, ∀ y ∈ Y, e x y → rowPoint x y ∈ G) :
    (∑ x ∈ F, ((Y.filter fun y => e x y).card:ℝ)) ≤
      (Q.card:ℝ)*K*(R+S)^t*(G.card:ℝ) := by
  classical
  let A := (F ×ˢ Y).filter fun p => e p.1 p.2
  let H := A.image fun p => rowPoint p.1 p.2
  have hcard : H.card = ∑ x ∈ F, (Y.filter fun y => e x y).card := by
    rw [show H.card = A.card from Finset.card_image_of_injective _ rowPoint_pair_injective]
    simp only [A,Finset.card_filter,Finset.sum_product]
  let B := fun q => G.filter fun p => dist p (rowPoint z q) ≤ R+S
  have hsub : H ⊆ Q.biUnion B := by
    intro p hp
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hxy,he⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨q,hq,hyq⟩ := hcover y hy
    exact Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_filter.mpr
      ⟨hgraph x hx y hy he,rowPoint_dist_le_sum hR hS (hF x hx) hyq⟩⟩
  have hc : (H.card:ℝ) ≤ ∑ q ∈ Q, ((B q).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hb (q : ℝ) : ((B q).card:ℝ) ≤ K*(R+S)^t*(G.card:ℝ) :=
    normalized_ball_bound_all_radii ht hK hreg _ _ hδ
  calc
    _ = (H.card:ℝ) := by rw [hcard,Nat.cast_sum]
    _ ≤ ∑ q ∈ Q, ((B q).card:ℝ) := hc
    _ ≤ ∑ _q ∈ Q, K*(R+S)^t*(G.card:ℝ) := Finset.sum_le_sum fun q _ => hb q
    _ = _ := by simp; ring

end Falconer

end OAI
