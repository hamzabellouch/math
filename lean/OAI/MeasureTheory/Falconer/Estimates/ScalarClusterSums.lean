import OAI.MeasureTheory.Falconer.Radial.ScalarAffineExceptions
import OAI.MeasureTheory.Falconer.Estimates.ScalarEnergyRefinement

namespace OAI

/-! Disjoint scalar projection cells outside the explicitly bounded
 exceptional coefficient set. The children are the actual original
 finite clusters, so their covering numbers can be iterated. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_cells_disjoint_of_centers {δ R c d : ℝ} (hδ : 0 < δ)
    (hR : δ ≤ R) (hcd : 5*R < |c-d|)
    (A B : Finset ℝ) (hA : ∀ x ∈ A, |x-c| ≤ 2*R)
    (hB : ∀ y ∈ B, |y-d| ≤ 2*R) :
    Disjoint (scalarCells δ A) (scalarCells δ B) := by
  apply Finset.disjoint_left.mpr
  intro k hkA hkB
  obtain ⟨x,hx,hxk⟩ := Finset.mem_image.mp hkA
  obtain ⟨y,hy,hyk⟩ := Finset.mem_image.mp hkB
  have hxy := same_scalar_cell_dist_lt hδ (hxk.trans hyk.symm)
  have ht : |c-d| ≤ |x-c|+|x-y|+|y-d| := by
    calc
      |c-d| = |(c-x)+(x-y)+(y-d)| := by congr 1; ring
      _ ≤ |c-x|+|x-y|+|y-d| := (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by rw [abs_sub_comm c x]
  have ha := hA x hx
  have hb := hB y hy
  linarith

 theorem scalar_cluster_sum_near {r b x y : ℝ} (hb : |b| ≤ 1)
    (A C : Finset ℝ) (hA : ∀ a ∈ A, |a-x| ≤ r)
    (hC : ∀ c ∈ C, |c-y| ≤ r) :
    ∀ z ∈ A+C.image (fun c => b*c), |z-(x+b*y)| ≤ 2*r := by
  intro z hz
  obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  calc
    |(a+b*c)-(x+b*y)| = |(a-x)+b*(c-y)| := by congr 1; ring
    _ ≤ |a-x|+|b*(c-y)| := abs_add_le _ _
    _ = |a-x|+|b| * |c-y| := by rw [abs_mul]
    _ ≤ r+1*r := add_le_add (hA a ha) (mul_le_mul hb (hC c hc) (abs_nonneg _) (by norm_num))
    _ = 2*r := by ring

 theorem scalar_cluster_sums_cells {δ r b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hb : |b| ≤ 1)
    (hgood : b ∉ scalarBadClusterCoefficients B X Y (5*r))
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y, (scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card) ≤
      (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let W := fun p : ℝ × ℝ => scalarCells δ (U p.1+(V p.2).image (fun c => b*c))
  have hdis : ((X ×ˢ Y : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).PairwiseDisjoint W := by
    intro p hp q hq hpq
    have hc : 5*r < |(p.1+b*p.2)-(q.1+b*q.2)| := by
      by_contra hn
      apply hgood
      exact Finset.mem_filter.mpr ⟨hbB,p,hp,q,hq,hpq,le_of_not_gt hn⟩
    exact scalar_cells_disjoint_of_centers hδ hr hc _ _
      (scalar_cluster_sum_near hb _ _
        (hU p.1 (Finset.mem_product.mp hp).1) (hV p.2 (Finset.mem_product.mp hp).2))
      (scalar_cluster_sum_near hb _ _
        (hU q.1 (Finset.mem_product.mp hq).1) (hV q.2 (Finset.mem_product.mp hq).2))
  have hsub : (X ×ˢ Y).biUnion W ⊆
      scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c)) := by
    intro k hk
    obtain ⟨p,hp,hkp⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hkp
    obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨a+b*c,Finset.add_mem_add ?_ ?_,rfl⟩
    · exact Finset.mem_biUnion.mpr ⟨p.1,(Finset.mem_product.mp hp).1,ha⟩
    · exact Finset.mem_image.mpr ⟨c,Finset.mem_biUnion.mpr
        ⟨p.2,(Finset.mem_product.mp hp).2,hc⟩,rfl⟩
  exact (Finset.card_biUnion hdis).symm.trans_le (Finset.card_le_card hsub)

end Falconer

end OAI
