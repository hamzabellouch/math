import OAI.Geometry.RCD.Transport.PointedMidpointSets

namespace OAI

/-! # Quantitative thickening of midpoint sets -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

theorem thickening_subset_ball_of_subset_closedBall {n : ℕ}
    {A : Set (Euclidean n)} {a δ : ℝ} (hA : A ⊆ closedBall 0 a) :
    thickening δ A ⊆ ball 0 (a+δ) := by
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
  have hy0 := mem_closedBall.mp (hA hy)
  have ht := dist_triangle x y 0
  exact mem_ball.mpr (by linarith only [hxy,hy0,ht])

theorem midpointSet_thickening_subset {n : ℕ}
    (A B : Set (Euclidean n)) (δ : ℝ) :
    midpointSet (thickening δ A) (thickening δ B) ⊆
      thickening δ (midpointSet A B) := by
  rintro x ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
  obtain ⟨a',ha',haa⟩ := mem_thickening_iff.mp ha
  obtain ⟨b',hb',hbb⟩ := mem_thickening_iff.mp hb
  apply mem_thickening_iff.mpr
  refine ⟨(1/2:ℝ) • (a'+b'),⟨(a',b'),⟨ha',hb'⟩,rfl⟩,?_⟩
  rw [dist_eq_norm,← smul_sub,norm_smul,
    Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have he : a+b-(a'+b')=(a-a')+(b-b') := by abel
  rw [he]
  have ht := norm_add_le (a-a') (b-b')
  rw [dist_eq_norm] at haa hbb
  linarith only [ht,haa,hbb]

theorem cthickening_midpointSet_thickening_subset {n : ℕ}
    (A B : Set (Euclidean n)) {κ δ : ℝ} (hκ : 0 ≤ κ) :
    cthickening κ (midpointSet (thickening δ A) (thickening δ B)) ⊆
      cthickening (κ+δ) (midpointSet A B) :=
  (cthickening_subset_of_subset κ (midpointSet_thickening_subset A B δ)).trans
    (cthickening_thickening_subset hκ δ (midpointSet A B))

end RegularPointCoordinates

end

end OAI
