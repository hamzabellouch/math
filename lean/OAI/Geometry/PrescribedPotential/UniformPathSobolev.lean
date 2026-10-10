import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPathContinuation
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.PathLaplacianSobolev
import OAI.Geometry.PrescribedPotential.PointPoisson
import OAI.Geometry.PrescribedPotential.RealSmoothOperator

namespace OAI

/-! Uniform Path Sobolev. -/

section

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma pointPoissonOrder_laplacian (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X)
    (φ : SmoothRealFunction A) (hn : φ.value x₀ = 0) :
    D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ) =
      D.pointPoissonOrder m hm he P k x₀ (D.localizers.embed (k : ℝ) (Smooth.ofReal (g.laplacian φ))) := by
  let F := D.localizers.embed (k : ℝ) (Smooth.ofReal (g.laplacian φ))
  apply (D.pointPoissonOrder_unique m hm he k hk x₀ _ _ 0
    (D.poissonResidue m hm he P (D.localizers.lower (k : ℝ) 0 F)) ?_ ?_).1
  · rw [map_zero,sub_zero,D.completedLOrder_embed,complexL_ofReal,D.pointPoissonOrder_equation]
    exact (add_sub_cancel_right F _).symm
  · rw [D.pointEvaluation_embed hk,D.pointPoissonOrder_normalized m hm he P k hk]
    simp only [Smooth.ofReal_apply,hn,Complex.ofReal_zero]

lemma normalized_sobolev_laplacian_estimate (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X)
    (r : ℝ) (hr : r ≤ (k : ℝ)+2) (φ : SmoothRealFunction A) (hn : φ.value x₀ = 0) :
    ‖D.localizers.embed r (Smooth.ofReal φ)‖ ≤
      ‖D.localizers.lower ((k : ℝ)+2) r‖ *
        (‖D.pointPoissonOrder m hm he P k x₀‖ *
          ‖D.localizers.embed (k : ℝ) (Smooth.ofReal (g.laplacian φ))‖) := by
  have hv := D.pointPoissonOrder_laplacian m hm he P k hk x₀ φ hn
  have hhigh : ‖D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ)‖ ≤
      ‖D.pointPoissonOrder m hm he P k x₀‖ *
          ‖D.localizers.embed (k : ℝ) (Smooth.ofReal (g.laplacian φ))‖ := by
    rw [hv]
    exact (D.pointPoissonOrder m hm he P k x₀).le_opNorm _
  calc
    _ = ‖D.localizers.lower ((k : ℝ)+2) r (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))‖ :=
      congrArg norm (D.localizers.lower_embed hr (Smooth.ofReal φ)).symm
    _ ≤ ‖D.localizers.lower ((k : ℝ)+2) r‖ * ‖D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ)‖ :=
      (D.localizers.lower ((k : ℝ)+2) r).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left hhigh (norm_nonneg (D.localizers.lower ((k : ℝ)+2) r))

 

theorem pathSobolevBounds (h : SemipositiveAnticanonicalMetric A) (x₀ : X) :
    D.PathSobolevBounds h x₀ := by
  obtain ⟨m,hm,he⟩ := D.exists_completedError_small
  obtain ⟨P⟩ := D.localizers.constantProjection_exists
  intro k
  let j : ℕ := 2*k + Module.finrank ℝ (EC d)
  have hj : (Module.finrank ℝ (EC d) : ℝ) < 2*((j : ℝ)+2) := by
    dsimp [j]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k,Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EC d))]
  have hkj : (((2*k : ℕ) : ℝ)+2) ≤ ((j : ℝ)+2) := by
    dsimp [j]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EC d))]
  obtain ⟨C,hC⟩ := path_laplacian_sobolev_bound g h D.localizers (j : ℝ)
  refine ⟨‖D.localizers.lower ((j : ℝ)+2) (((2*k : ℕ) : ℝ)+2)‖ *
    (‖D.pointPoissonOrder m hm he P j x₀‖*C),fun t b φ ht hn hs => ?_⟩
  let s : PathSolution g h := ⟨t,b,φ,ht,hs⟩
  exact (D.normalized_sobolev_laplacian_estimate m hm he P j hj x₀
    (((2*k : ℕ) : ℝ)+2) hkj φ hn).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hC s) (norm_nonneg (D.pointPoissonOrder m hm he P j x₀)))
      (norm_nonneg (D.localizers.lower ((j : ℝ)+2) (((2*k : ℕ) : ℝ)+2))))
end GluingData
end GlobalElliptic

end
end

end OAI
