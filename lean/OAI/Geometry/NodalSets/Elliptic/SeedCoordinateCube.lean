import OAI.Geometry.NodalSets.Charts.SeedMetricNeighborhood

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

def seedCoordinateCube (a : ℝ) : Set BaseModel := {y | ∀ i, |y i| ≤ a}

lemma seedCoordinateCube_closed (a : ℝ) : IsClosed (seedCoordinateCube a) := by
  simpa [seedCoordinateCube,Set.ofPred_forall,EuclideanSpace.proj] using
    isClosed_iInter (fun i : Fin 4 ↦ isClosed_le (EuclideanSpace.proj i).continuous.abs
      (continuous_const (y := a)))

lemma seedCoordinateCube_norm {a : ℝ} (ha : 0 ≤ a) {y : BaseModel}
    (hy : y ∈ seedCoordinateCube a) : ‖y‖ ≤ 2*a := by
  have hs (i : Fin 4) : (y i)^2 ≤ a^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (y i)) ha).mpr (hy i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hs i)
  rw [← EuclideanSpace.real_norm_sq_eq] at hsum
  norm_num at hsum
  nlinarith [norm_nonneg y]

lemma seedCoordinateCube_compact {a : ℝ} (ha : 0 ≤ a) : IsCompact (seedCoordinateCube a) := by
  apply (isCompact_closedBall (0 : BaseModel) (2*a)).of_isClosed_subset (seedCoordinateCube_closed a)
  intro y hy
  rw [mem_closedBall,dist_zero_right]
  exact seedCoordinateCube_norm ha hy

lemma seedCoordinateCube_zero {a : ℝ} (ha : 0 ≤ a) : (0 : BaseModel) ∈ seedCoordinateCube a := by
  intro i
  simpa using ha

theorem seed_metric_patch_cube : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (closedBall (0 : BaseModel) r) ∧ IsCompact (seedCoordinateCube a) ∧
    seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ g : BaseModel → BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ,
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((g y,fderiv ℝ g y) : MetricJet BaseModel) (roundMetricJet y) < δ) →
      ∀ y ∈ closedBall (0 : BaseModel) r,
        JetAdmissible seedRealChart (g y,fderiv ℝ g y) y := by
  obtain ⟨r,δ,hr,hδ,hcompact,hbranch,hg⟩ := seed_uniform_metric_neighborhood
  refine ⟨r,r/4,δ,hr,by positivity,hδ,hcompact,seedCoordinateCube_compact (by positivity),?_,hbranch,hg⟩
  intro y hy
  rw [mem_ball,dist_zero_right]
  have hn := seedCoordinateCube_norm (a := r/4) (by positivity) hy
  linarith

end
end Yau.Target

end OAI
