import OAI.Geometry.RCD.Metric.EuclideanInteriorSmoothExtension
import OAI.Geometry.RCD.Metric.EuclideanGreenIdentity

namespace OAI

/-! # Compact tests that agree exactly with Euclidean coordinates -/

open Set Metric Filter InnerProductSpace Laplacian
open scoped ContDiff Topology
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_coordinate_laplacian {n : ℕ} (i : Fin n) :
    Δ (fun x : Euclidean n => x i)=0 := by
  have hs : ContDiff ℝ 2 (fun x : Euclidean n => x i) :=
    (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).contDiff
  rw [laplacian_eq_sum_second_directional hs]
  funext x
  have he : ∀ z : Euclidean n, fderiv ℝ (fun y : Euclidean n => y i) z=EuclideanSpace.proj i :=
    fun z => (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt.fderiv
  simp_rw [he]
  simp

theorem euclidean_coordinate_harmonic {n : ℕ} (i : Fin n) :
    HarmonicOnNhd (fun x : Euclidean n => x i) univ := by
  intro x _
  exact ⟨(EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).contDiff.contDiffAt,
    Filter.Eventually.of_forall fun y => congrFun (euclidean_coordinate_laplacian i) y⟩

theorem compact_euclidean_coordinate_test {n : ℕ} {R S : ℝ}
    (hR : 0<R) (hRS : R<S) (i : Fin n) :
    ∃ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ ∧
      EqOn ψ (fun x => x i) (closedBall 0 R) ∧
      EqOn (fderiv ℝ ψ) (fun _ => (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)) (ball 0 R) ∧
      HarmonicOnNhd ψ (ball 0 R) := by
  obtain ⟨ψ,hψ,heq,hd⟩ := exists_interior_smooth_extension hR hRS
    (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).contDiff.contDiffOn
  refine ⟨ψ,hψ,heq,?_,?_⟩
  · intro x hx
    exact (hd hx).trans (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt.fderiv
  · intro x hx
    have he : ψ=ᶠ[𝓝 x] (fun y : Euclidean n => y i) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact heq (ball_subset_closedBall hy)
    exact (harmonicAt_congr_nhds he).mpr (euclidean_coordinate_harmonic i x (mem_univ x))

end RegularPointCoordinates

end

end OAI
