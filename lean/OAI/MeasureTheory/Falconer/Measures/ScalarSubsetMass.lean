import OAI.MeasureTheory.Falconer.Geometry.ScalarGrowthOfCover

namespace OAI

/-! Relative ball bounds and projection covers under the actual scalar
 pruning. The sole cost is the ratio of the numbers of retained leaves. -/
namespace Falconer
open scoped Pointwise

 theorem scalarBallMass_mono {A B : Finset ℝ} (h : A ⊆ B) (u r : ℝ) :
    scalarBallMass A u r ≤ scalarBallMass B u r := by
  unfold scalarBallMass
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h)

 theorem scalar_projection_cover_mono {A B : Finset ℝ} (h : A ⊆ B) (δ t : ℝ) :
    (scalarCells δ (A+A.image (fun x => t*x))).card ≤
      (scalarCells δ (B+B.image (fun x => t*x))).card := by
  exact Finset.card_le_card (Finset.image_subset_image
    (Finset.add_subset_add h (Finset.image_subset_image h)))

namespace Regularization

 theorem scalar_leaf_center_card {N : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) : (Q.image scalarPathCenter).card = Q.card := by
  exact Finset.card_image_of_injOn (scalarPathCenter_injOn Q
    (fun q hq => (mem_cubePaths 1 N q).mp (hQ hq)))

 theorem scalar_pruned_ball_bound {N : ℕ} {L Q : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hQL : Q ⊆ L) {R K κ : ℝ} (hK : 0 ≤ K)
    (hsize : (L.card:ℝ) ≤ R*(Q.card:ℝ))
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K*t^κ*((L.image scalarPathCenter).card:ℝ)) :
    ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass (Q.image scalarPathCenter) u t ≤
        (K*R)*t^κ*((Q.image scalarPathCenter).card:ℝ) := by
  intro u t ht ht1
  have hm := scalarBallMass_mono (Finset.image_subset_image (f := scalarPathCenter) hQL) u t
  have hh := hball u t ht ht1
  rw [scalar_leaf_center_card L hL] at hh
  rw [scalar_leaf_center_card Q (hQL.trans hL)]
  have hp := mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg (by
    exact (pow_pos (by norm_num : (0:ℝ) < 1/2) N).le.trans ht) κ))
  nlinarith

end Regularization
end Falconer

end OAI
