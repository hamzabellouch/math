import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ExpLocalBounds
import OAI.Analysis.BiholderTransport.Coordinates.RadialFactor
import OAI.Analysis.BiholderTransport.LinearAlgebra.PositiveSingular

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section CrossingUniform
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma compact_bundle_radialCrossingValue_bounds
    {K : Set (TangentBundle 𝓘(ℝ,Model n) M)} (hK : IsCompact K)
    (hI : ∀ z∈K, z.2∈injectivityDomain z.1) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ z∈K, ∀ v : TangentSpace 𝓘(ℝ,Model n) z.1,
      c*‖v‖^2≤radialCrossingValue z.1 z.2 v ∧
      radialCrossingValue z.1 z.2 v≤C*‖v‖^2 := by
  have hR : IsCompact (reverseRay '' K) := hK.image continuous_reverseRay
  have hRI : ∀ r∈reverseRay '' K, r.2∈injectivityDomain r.1 := by
    rintro r ⟨z,hz,rfl⟩
    exact reverseRay_injectivityDomain (hI z hz)
  obtain ⟨l,u,hl,hu,H⟩ := compact_exp_differential_bounds hR hRI
  refine ⟨(u^2)⁻¹,(l^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hu),inv_pos.mpr (sq_pos_of_pos hl),?_⟩
  intro z hz v
  obtain ⟨L,hL,hN,hD⟩ := normalHessian_radial_derivative_factor (hI z hz)
  have heq : radialCrossingValue z.1 z.2 v=‖L v‖^2 := by
    have hd := (hD v).unique (normalHessian_radial_derivative_value (hI z hz) v)
    linarith
  have hb := H (reverseRay z) (mem_image_of_mem _ hz) (L v)
  rw [hN] at hb
  rw [heq]
  constructor
  · have hs : ‖v‖^2≤u^2*‖L v‖^2 := by
      nlinarith [sq_le_sq₀ (norm_nonneg v) (mul_nonneg hu.le (norm_nonneg (L v))) |>.mpr hb.2]
    rw [inv_mul_le_iff₀ (sq_pos_of_pos hu)]
    exact hs
  · have hs : l^2*‖L v‖^2≤‖v‖^2 := by
      nlinarith [sq_le_sq₀ (mul_nonneg hl.le (norm_nonneg (L v))) (norm_nonneg v) |>.mpr hb.1]
    rw [le_inv_mul_iff₀ (sq_pos_of_pos hl)]
    exact hs

end CrossingUniform
end WeakMTWTransport

end

end

end

end OAI
