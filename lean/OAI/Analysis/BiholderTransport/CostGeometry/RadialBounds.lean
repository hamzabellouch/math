import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ScaledSpectrum
import OAI.Analysis.BiholderTransport.LinearAlgebra.ScaledQuadraticBoundEigenvalues

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff BigOperators

namespace WeakMTWTransport
section RadialBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_radial_defect_quadratic_bounds :
    ∃ C : ℝ, 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ δ∈Ioc (0:ℝ) (1/2), ∀ v,
      -C*δ*‖v‖^2 ≤ radialHessianDefectBilinear x p δ v v ∧
      |radialHessianDefectBilinear x p δ v v| ≤ C*‖v‖^2 := by
  obtain ⟨l,u,B,hl,hu,hB,H⟩ := uniform_radial_inverse_profile (n := n) (M := M)
  refine ⟨u+B,add_pos hu hB,?_⟩
  intro x p hp δ hd v
  obtain ⟨K,hK,hKb,hBg,hSp⟩ := H x p hp δ hd
  have hku : δ*inner ℝ (K v) v ≤ u*‖v‖^2 := by
    refine scaled_quadratic_bound_of_eigenvalues (n := Module.finrank ℝ (Model n))
      hK.isSymmetric rfl ?_ v
    intro i
    have hs := (endpointExpDifferential x p).toLinearMap.singularValues_nonneg i.rev
    refine (hSp i).2.trans ?_
    rw [div_le_iff₀ (add_pos_of_nonneg_of_pos hs hd.1)]
    nlinarith [mul_nonneg hu.le hs]
  have hk0 : 0 ≤ δ*inner ℝ (K v) v := mul_nonneg hd.1.le (hK.inner_nonneg_left v)
  have hb := abs_le.mp (hBg v)
  have hdn : B*δ*‖v‖^2 ≤ B*‖v‖^2 := by
    have hh := mul_le_mul_of_nonneg_right (show δ ≤ 1 by linarith [hd.2])
      (mul_nonneg hB.le (sq_nonneg ‖v‖))
    nlinarith only [hh]
  have hun := mul_nonneg hu.le (sq_nonneg ‖v‖)
  have hud := mul_nonneg hu.le (mul_nonneg hd.1.le (sq_nonneg ‖v‖))
  constructor
  · nlinarith only [hb.1,hk0,hud]
  · apply abs_le.mpr
    constructor <;> nlinarith only [hb.1,hb.2,hk0,hku,hdn,hun]
end RadialBounds
end WeakMTWTransport

end

end

end

end OAI
