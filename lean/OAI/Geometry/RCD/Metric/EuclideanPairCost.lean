import OAI.Geometry.RCD.Metric.EuclideanPairCompactness

namespace OAI

/-! # Quadratic endpoint cost on a uniformly bounded family of pair laws -/

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

def boundedPairCost {n : ℕ} (B : ℝ) : (Euclidean n × Euclidean n) →ᵇ ℝ := by
  let f := fun z : Euclidean n × Euclidean n => min (dist z.1 z.2^2) (4*B^2)
  have hf : Continuous f := ((continuous_fst.dist continuous_snd).pow 2).min continuous_const
  have hnon (z : Euclidean n × Euclidean n) : 0≤f z := le_min (sq_nonneg _) (by positivity)
  refine ⟨⟨f,hf⟩,8*B^2,?_⟩
  intro x y
  calc dist (f x) (f y)≤dist (f x) 0+dist 0 (f y) := dist_triangle _ _ _
    _ = f x+f y := by simp only [dist_zero_right,dist_zero_left,Real.norm_eq_abs,
      abs_of_nonneg (hnon x),abs_of_nonneg (hnon y)]
    _ ≤ 8*B^2 := by
      dsimp only [f]
      have hx := min_le_right (dist x.1 x.2^2) (4*B^2)
      have hy := min_le_right (dist y.1 y.2^2) (4*B^2)
      linarith only [hx,hy]

theorem boundedPairCost_eq {n : ℕ} {B : ℝ} (hB : 0≤B) {x y : Euclidean n}
    (hx : x∈closedBall 0 B) (hy : y∈closedBall 0 B) :
    boundedPairCost B (x,y)=dist x y^2 := by
  change min (dist x y^2) (4*B^2)=_
  have hd : dist x y≤2*B := by
    have hh := dist_triangle x 0 y
    have hx' : dist x 0≤B := hx
    have hy' : dist 0 y≤B := by rw [dist_comm]; exact hy
    linarith
  apply min_eq_left
  have hh := (sq_le_sq₀ dist_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hB)).mpr hd
  nlinarith

theorem bounded_pair_cost_tendsto {n : ℕ} {B : ℝ} (hB : 0≤B)
    (νs : ℕ → ProbabilityMeasure (Euclidean n × Euclidean n))
    (ν : ProbabilityMeasure (Euclidean n × Euclidean n))
    (hlim : Tendsto νs atTop (𝓝 ν))
    (hbs : ∀ k, ∀ᵐ z ∂(νs k : Measure (Euclidean n × Euclidean n)),
      z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B)
    (hb : ∀ᵐ z ∂(ν : Measure (Euclidean n × Euclidean n)),
      z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B) :
    Tendsto (fun k => ∫ z, dist z.1 z.2^2 ∂(νs k : Measure (Euclidean n × Euclidean n))) atTop
      (𝓝 (∫ z, dist z.1 z.2^2 ∂(ν : Measure (Euclidean n × Euclidean n)))) := by
  have he (ρ : ProbabilityMeasure (Euclidean n × Euclidean n))
      (hρ : ∀ᵐ z ∂(ρ : Measure (Euclidean n × Euclidean n)),
        z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B) :
      (∫ z, boundedPairCost B z ∂(ρ : Measure (Euclidean n × Euclidean n)))=
        ∫ z, dist z.1 z.2^2 ∂(ρ : Measure (Euclidean n × Euclidean n)) := by
    apply integral_congr_ae
    filter_upwards [hρ] with z hz
    exact boundedPairCost_eq hB hz.1 hz.2
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (boundedPairCost B)
  simpa only [he ν hb,he _ (hbs _)] using ht

end RegularPointCoordinates

end

end OAI
