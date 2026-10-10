import OAI.Analysis.CircleDomains.Sobolev.SquareAverageComparison

namespace OAI

/-! Uniform square mean-oscillation bounds give a quantitative Lipschitz restriction. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma square_oscillation_lipschitzOn {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {S : Set (ℝ × ℝ)} (M : ℝ≥0)
    (hosc : ∀ c ∈ S, ∀ r > 0,
      (⨍ p in coordinateSquare c r, |f p-squareAverage f c r|) ≤ (M:ℝ)*r) :
    LipschitzOnWith (32*M) f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases heq : x = y
  · simp [heq]
  let r := dist x y
  have hr : 0 < r := dist_pos.mpr heq
  have hxr : |f x-squareAverage f x (2*r)| ≤ 8*(M:ℝ)*(2*r) :=
    square_point_average_bound hf x (by positivity) (fun n =>
      hosc x hx _ (mul_pos (by positivity) (pow_pos (by norm_num) n)))
  have hyr : |f y-squareAverage f y r| ≤ 8*(M:ℝ)*r :=
    square_point_average_bound hf y hr (fun n =>
      hosc y hy _ (mul_pos hr (pow_pos (by norm_num) n)))
  have hsub : coordinateSquare y r ⊆ coordinateSquare x (2*r) :=
    closedBall_subset_closedBall' (by dsimp only [r]; rw [dist_comm y x]; linarith)
  have hcomp := squareAverage_comparison hf hr (by positivity : 0 < 2*r) hsub (le_refl _)
  have havg : |squareAverage f x (2*r)-squareAverage f y r| ≤ 8*(M:ℝ)*r := by
    rw [abs_sub_comm]
    calc
      _ ≤ 4*(⨍ p in coordinateSquare x (2*r), |f p-squareAverage f x (2*r)|) := hcomp
      _ ≤ 4*((M:ℝ)*(2*r)) := mul_le_mul_of_nonneg_left (hosc x hx _ (by positivity)) (by norm_num)
      _ = _ := by ring
  have htriangle : |f x-f y| ≤ |f x-squareAverage f x (2*r)| +
      |squareAverage f x (2*r)-squareAverage f y r| + |squareAverage f y r-f y| := by
    calc
      _ ≤ |f x-squareAverage f x (2*r)|+|squareAverage f x (2*r)-f y| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [abs_sub_le (squareAverage f x (2*r)) (squareAverage f y r) (f y)]
  rw [abs_sub_comm (squareAverage f y r) (f y)] at htriangle
  change |f x-f y| ≤ _
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  change |f x-f y| ≤ 32*(M:ℝ)*r
  linarith

lemma locally_sobolev_lipschitzOn_of_square_averages {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {S : Set (ℝ × ℝ)} (B : ℝ≥0)
    (havg : ∀ c ∈ S, ∀ r > 0, (⨍ p in coordinateSquare c r,
      |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) ≤ B) :
    LipschitzOnWith (64*B) (fun p => u (euclideanPlaneCoordinates.symm p)) S := by
  have ho : ∀ c ∈ S, ∀ r > 0,
      (⨍ p in coordinateSquare c r, |u (euclideanPlaneCoordinates.symm p)-
        squareAverage (fun p => u (euclideanPlaneCoordinates.symm p)) c r|) ≤ (2*B:ℝ≥0)*r := by
    intro c hc r hr
    calc
      _ ≤ 2*r*(⨍ p in coordinateSquare c r,
          |V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|) :=
        locally_sobolev_square_poincare hu hw hLp c hr
      _ ≤ 2*r*(B:ℝ) := mul_le_mul_of_nonneg_left (havg c hc r hr) (by positivity)
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  convert square_oscillation_lipschitzOn (hu.comp euclideanPlaneCoordinates.symm.continuous)
    (2*B) ho using 1
  · ring
  · rfl

end CircleDomainRigidity

end

end OAI
