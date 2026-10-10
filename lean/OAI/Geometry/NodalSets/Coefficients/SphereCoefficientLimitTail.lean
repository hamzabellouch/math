import OAI.Geometry.NodalSets.SmoothLimit.FiniteJetSummableTailLemmas
import OAI.Geometry.NodalSets.SmoothLimit.SphereSummableChartLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Set Filter Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sphereAtlasCore_subset_closure_interior :
    sphereAtlasCore ⊆ closure (interior sphereAtlasCore) := by
  rintro z ⟨y,hy,rfl⟩
  have hy' : y ∈ closure (ball (0 : Yau.Jets.Coord) 1) := by
    rw [closure_ball _ one_ne_zero]
    exact hy
  apply closure_mono (s := seedCoordEquiv '' ball (0 : Yau.Jets.Coord) 1) ?_
    (mem_closure_image seedCoordEquiv.continuous.continuousAt hy')
  exact (seedCoordEquiv.isOpenMap _ isOpen_ball).subset_interior_iff.mpr
    (image_mono ball_subset_closedBall)

theorem sphere_coefficient_limit_tail (P : Finset Base) (J : ℕ)
    (d : ℕ → SphereEnergyData) (a : SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a.density)
    (hpoint : ∀ p ∈ P, ∀ z ∈ interior sphereAtlasCore,
      Tendsto (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p z)
        atTop (𝓝 (intrinsicChartCoefficient a.tensor a.density p z)))
    (hseq : Summable (fun n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density)) :
    Tendsto (fun n ↦ sphereCoefficientDistance P J (d n).tensor (d n).density a.tensor a.density)
      atTop (𝓝 0) ∧
    ∀ n, sphereCoefficientDistance P J (d n).tensor (d n).density a.tensor a.density ≤
      ∑' j, sphereCoefficientDistance P J (d (n+j)).tensor (d (n+j)).density
        (d (n+j+1)).tensor (d (n+j+1)).density := by
  let b : ℕ → ℝ := fun n ↦ sphereCoefficientDistance P J
    (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density
  have hds (n : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d n).tensor (d n).smooth (d n).symm (d n).pos (d n).density (hd n) p
  have has (p : Base) := intrinsic_coefficient_chart_smooth
    a.tensor a.smooth a.symm a.pos a.density ha p
  have hnonneg (n : ℕ) : 0 ≤ b n := sphereCoefficientDistance_nonneg P J
    (d n).tensor (d (n+1)).tensor (d n).density (d (n+1)).density
    (fun p _ ↦ hds n p) (fun p _ ↦ hds (n+1) p)
  have hjet (p : Base) (hp : p ∈ P) := finite_jet_summable_tail
    (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p)
    (intrinsicChartCoefficient a.tensor a.density p) (fun n ↦ hds n p) (has p)
    sphereAtlasCore sphereAtlasCore_subset_closure_interior (hpoint p hp) J b hseq
    (fun k hk n z hz ↦ sphere_coefficient_jet_increment_bound P J (d n) (d (n+1))
      (hd n) (hd (n+1)) p hp k hk z hz)
  have htail (n : ℕ) : sphereCoefficientDistance P J (d n).tensor (d n).density a.tensor a.density ≤
      ∑' j, b (n+j) := by
    apply finiteChartDerivativeSize_le _ _ _ _ (tsum_nonneg (fun j ↦ hnonneg (n+j)))
    intro p hp k hk z hz
    rw [fun_iteratedFDeriv_sub_apply
      ((has p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      ((hds n p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
    simpa only [dist_eq_norm,norm_sub_rev] using (hjet p hp k hk).2 n z hz
  refine ⟨?_,htail⟩
  apply squeeze_zero (fun n ↦ sphereCoefficientDistance_nonneg P J
    (d n).tensor a.tensor (d n).density a.density (fun p _ ↦ hds n p) (fun p _ ↦ has p)) htail
  simpa only [Nat.add_comm] using tendsto_sum_nat_add b

end
end Yau.Target

end OAI
