import OAI.MeasureTheory.Falconer.Estimates.ScalarGroupOverlap
import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterWeights

namespace OAI

/-! Positive projection weights for arbitrary total branching, after
 fixing one column group and summing all horizontal groups. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_grouped_weighted_cells {δ r μ η b z w : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hgap : 5*r < μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hYne : Y.Nonempty)
    (j : ℤ) (hYgrid : ∀ y ∈ Y, ⌊(y-w)/η⌋ = j)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y,
      scalarCollisionWeight (Y.card : ℝ)
        (scalarBadClusterCoefficients B (scalarGridFiber η z X ⌊(p.1-z)/η⌋) Y (5*r)) b *
        ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      9*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  let I := X.image (fun x => ⌊(x-z)/η⌋)
  let G := fun k => scalarGridFiber η z X k
  let W := fun k => scalarCollisionWeight (Y.card : ℝ) (scalarBadClusterCoefficients B (G k) Y (5*r)) b
  let Q := fun x y => ((scalarCells δ (U x+(V y).image (fun c => b*c))).card : ℝ)
  have hb : |b| ≤ 1 := by rwa [abs_of_nonneg hb0]
  have hk (k : ℤ) : W k*(∑ p ∈ G k ×ˢ Y, Q p.1 p.2) ≤
      ((scalarCells δ (((G k).biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact scalar_cluster_weighted_cells hδ hδr hgap hb B (G k) Y hbB hYne
      (fun x hx x' hx' hne => hXsep x (Finset.mem_filter.mp hx).1 x' (Finset.mem_filter.mp hx').1 hne)
      U V (fun x hx => hU x (Finset.mem_filter.mp hx).1) hV
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ I) => hk k)
  have he : (∑ k ∈ I, W k*(∑ p ∈ G k ×ˢ Y, Q p.1 p.2)) =
      ∑ p ∈ X ×ˢ Y, W ⌊(p.1-z)/η⌋*Q p.1 p.2 := by
    simp only [Finset.sum_product,Finset.mul_sum]
    exact scalar_grid_sum η z X (fun k x => ∑ y ∈ Y, W k*Q x y)
  rw [he] at hs
  have ho : (∑ k ∈ I, ((scalarCells δ (((G k).biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) ≤
      9*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact_mod_cast scalar_group_projection_overlap hδ hη hδr hrη hb0 hb1 X Y j hYgrid U V hU hV I
  exact hs.trans ho

end Falconer

end OAI
