import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence
import OAI.Geometry.NodalSets.Charts.SphereFiniteChartEnergyUpper

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem sphere_C1_energy_cauchy (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r)) :
    CauchySeq u := by
  obtain ⟨K,hK,H⟩ := sphere_finite_chart_energy_upper d P r hcover
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨a,ha,haeps⟩ := exists_pos_mul_lt (sq_pos_of_pos heps) K
  let delta := min a 1
  have hdelta : 0 < delta := lt_min ha zero_lt_one
  have hd1 : delta ≤ 1 := min_le_right _ _
  have hda : delta ≤ a := min_le_left _ _
  have hsmall : K*delta^2 < eps^2 := by
    have hs : delta^2 ≤ delta := by nlinarith
    exact ((mul_le_mul_of_nonneg_left hs hK.le).trans
      (mul_le_mul_of_nonneg_left hda hK.le)).trans_lt haeps
  have hvals := Metric.tendstoUniformly_iff.mp ht (delta/2) (by positivity)
  have hder (p : P) (i : Fin 4) := Metric.tendstoUniformlyOn_iff.mp
    (hjet p p.property i) (delta/2) (by positivity)
  have hall : ∀ᶠ j in atTop, (∀ x, dist (v x) ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) x) < delta/2) ∧
      ∀ p : P, ∀ i : Fin 4, ∀ x ∈ ball (0 : Yau.Jets.Coord) r,
        dist (partialJet (v ∘ sphereChartCoordMap p) [i] x)
          (partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i] x) < delta/2 :=
    hvals.and (Filter.eventually_all.mpr (fun p ↦ Filter.eventually_all.mpr (hder p)))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hall
  refine ⟨M,fun j hj k hk ↦ ?_⟩
  have hv : ∀ x : Base, |(SphereEnergySmooth.toSmooth d (u j-u k) : Base → ℝ) x| ≤ delta := by
    intro x
    have h1 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM j hj).1 x)
    have h2 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM k hk).1 x)
    change |(SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) x-
      (SphereEnergySmooth.toSmooth d (u k) : Base → ℝ) x| ≤ delta
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hderiv : ∀ p ∈ P, ∀ x ∈ ball (0 : Yau.Jets.Coord) r, ∀ i : Fin 4,
      |partialJet ((SphereEnergySmooth.toSmooth d (u j-u k) : Base → ℝ) ∘ sphereChartCoordMap p) [i] x| ≤ delta := by
    intro p hp x hx i
    have h1 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM j hj).2 ⟨p,hp⟩ i x hx)
    have h2 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM k hk).2 ⟨p,hp⟩ i x hx)
    change |partialJet (fun y ↦ ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) y-
      ((SphereEnergySmooth.toSmooth d (u k) : Base → ℝ) ∘ sphereChartCoordMap p) y) [i] x| ≤ delta
    rw [partialJet_sub _ _ (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u j)).property p)
      (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u k)).property p)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hnorm := (H (u j-u k) delta hdelta.le hv hderiv).trans_lt hsmall
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (u j-u k)]

theorem sphere_C1_energy_completion_limit (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r)) :
    ∃ z : SphereEnergyHilbert d, Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z) := by
  apply cauchySeq_tendsto_of_complete
  exact (sphereEnergyToCompletion d).isometry.uniformContinuous.comp_cauchySeq
    (sphere_C1_energy_cauchy d P r hcover u v ht hjet)

end
end Yau.Target

end OAI
