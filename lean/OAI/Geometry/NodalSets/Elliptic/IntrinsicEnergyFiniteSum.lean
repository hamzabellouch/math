import OAI.Geometry.NodalSets.Elliptic.IntrinsicEnergyIntegrable

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma sphere_differential_pair_finite_sum {ι : Type*} [Fintype ι]
    (A : IntrinsicTensor) (f : ι → Base → ℝ) (g v : Base → ℝ)
    (hf : ∀ k, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f k))
    (hg : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ g) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (he : ∀ x, ∑ k, f k x = g x) (x : Base) :
    (∑ k, A x (sphereDifferential (f k) x) (sphereDifferential v x)) =
      A x (sphereDifferential g x) (sphereDifferential v x) := by
  classical
  have hd (y : Yau.Jets.Coord) (i : Fin 4) :
      Yau.coordPartial (g ∘ sphereChartCoordMap x) y i =
        ∑ k, Yau.coordPartial (f k ∘ sphereChartCoordMap x) y i := by
    have heq : g ∘ sphereChartCoordMap x = fun z ↦ ∑ k, (f k ∘ sphereChartCoordMap x) z := by
      funext z
      exact (he _).symm
    rw [heq]
    unfold Yau.coordPartial
    rw [fderiv_fun_sum (fun k _ ↦ (spherePullback_smooth (f k) (hf k) x).differentiable (by simp) y)]
    simp
  have hchart (y : Yau.Jets.Coord) :
      (∑ k, A (sphereChartCoordMap x y)
        (sphereDifferential (f k) (sphereChartCoordMap x y))
        (sphereDifferential v (sphereChartCoordMap x y))) =
      A (sphereChartCoordMap x y) (sphereDifferential g (sphereChartCoordMap x y))
        (sphereDifferential v (sphereChartCoordMap x y)) := by
    simp_rw [intrinsic_differential_pair_chart A _ v (hf _) hv,
      intrinsic_differential_pair_chart A g v hg hv,hd,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have h := hchart 0
  rw [sphereChartCoordMap_zero] at h
  exact h

end
end Yau.Target

end OAI
