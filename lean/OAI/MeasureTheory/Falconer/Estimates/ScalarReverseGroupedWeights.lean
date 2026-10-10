import OAI.MeasureTheory.Falconer.Estimates.ScalarGroupReverseOverlap
import OAI.MeasureTheory.Falconer.Estimates.ScalarReverseWeights

namespace OAI

/-! Grouped weights with a dense first-coordinate group. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_reverse_grouped_weighted_cells {δ r μ η b z w : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hgap : 15*r < μ) (hb0 : 1/3 ≤ b) (hb1 : b ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hXne : X.Nonempty)
    (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y,
      scalarCollisionWeight (X.card : ℝ)
        (scalarBadClusterCoefficients B X (scalarGridFiber η w Y ⌊(p.2-w)/η⌋) (5*r)) b *
        ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      17*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  let I := Y.image (fun y => ⌊(y-w)/η⌋)
  let G := fun k => scalarGridFiber η w Y k
  let W := fun k => scalarCollisionWeight (X.card : ℝ) (scalarBadClusterCoefficients B X (G k) (5*r)) b
  let Q := fun x y => ((scalarCells δ (U x+(V y).image (fun c => b*c))).card : ℝ)
  have hμ : 0 < μ := by have := hδ.trans_le hδr; linarith
  have hb : 0 ≤ b := by linarith
  have hbgap : 5*r < b*μ := by nlinarith
  have hk (k : ℤ) : W k*(∑ p ∈ X ×ˢ G k, Q p.1 p.2) ≤
      ((scalarCells δ ((X.biUnion U)+((G k).biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact scalar_cluster_reverse_weighted_cells hδ hδr hbgap hb hb1 B X (G k) hbB hXne
      (fun y hy y' hy' hne => hYsep y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hne)
      U V hU (fun y hy => hV y (Finset.mem_filter.mp hy).1)
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ I) => hk k)
  have he : (∑ k ∈ I, W k*(∑ p ∈ X ×ˢ G k, Q p.1 p.2)) =
      ∑ p ∈ X ×ˢ Y, W ⌊(p.2-w)/η⌋*Q p.1 p.2 := by
    simp only [Finset.sum_product,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _hx
    exact scalar_grid_sum η w Y (fun k y => W k*Q x y)
  rw [he] at hs
  have ho : (∑ k ∈ I, ((scalarCells δ ((X.biUnion U)+((G k).biUnion V).image (fun c => b*c))).card : ℝ)) ≤
      17*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact_mod_cast scalar_group_reverse_projection_overlap hδ hη hδr hrη hb0 X Y j hXgrid U V hU hV I
  exact hs.trans ho

end Falconer

end OAI
