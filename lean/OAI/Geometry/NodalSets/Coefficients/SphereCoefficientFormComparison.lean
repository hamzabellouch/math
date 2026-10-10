import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientDistanceLaws
import OAI.Geometry.NodalSets.Elliptic.CompactContravariantComparison

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma sphere_finite_atlas_coercivity (P : Finset Base)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ m > 0, ∀ p ∈ P, ∀ z ∈ sphereAtlasCore,
      (∀ alpha : BaseModel →L[ℝ] ℝ,
        m*‖alpha‖^2 ≤ alpha ((intrinsicChartCoefficient A rho p z).1 alpha)) ∧
      m ≤ (intrinsicChartCoefficient A rho p z).2 := by
  classical
  let : CompactSpace sphereAtlasCore := isCompact_iff_compactSpace.mp sphereAtlasCore_compact
  let c : {p // p ∈ P} × sphereAtlasCore → CoefficientPoint BaseModel :=
    fun t ↦ intrinsicChartCoefficient A rho t.1.val t.2.val
  have hc : Continuous c := continuous_prod_of_discrete_left.mpr
    (fun p ↦ (intrinsic_coefficient_chart_smooth A hA hs hp rho hr p.val).continuous.comp continuous_subtype_val)
  obtain ⟨m,hm,hbound,hrbound⟩ := compact_contravariant_margin c hc
    (fun t alpha hn ↦ intrinsicChartCoefficient_positive A hs hp rho t.1.val
      (by rw [centeredSphereChart_target]; trivial) alpha hn)
    (fun t ↦ hrp ((extChartAt (𝓡 4) t.1.val).symm t.2.val))
  exact ⟨m,hm,fun p hp z hz ↦ ⟨hbound (⟨p,hp⟩,⟨z,hz⟩),hrbound (⟨p,hp⟩,⟨z,hz⟩)⟩⟩

lemma sphereCoefficientDistance_value_bound (P : Finset Base) (J : ℕ)
    (A B : IntrinsicTensor) (rho sigma : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p))
    (p : Base) (hp : p ∈ P) (z : BaseModel) (hz : z ∈ sphereAtlasCore) :
    ‖intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z‖ ≤
      sphereCoefficientDistance P J A rho B sigma := by
  simpa only [sphereCoefficientDistance,norm_iteratedFDeriv_zero] using norm_le_finiteChartDerivativeSize P sphereAtlasCore_compact J
    (fun p z ↦ intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)
    (fun p hp ↦ (hB p hp).sub (hA p hp)) p hp 0 (Nat.zero_le _) z hz

theorem sphere_coefficient_relative_form_comparison (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta > 0, ∀ (B : IntrinsicTensor) (sigma : Base → ℝ),
      IntrinsicTensorSmooth B → (∀ x alpha beta, B x alpha beta = B x beta alpha) →
      (∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha) →
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ sigma →
      sphereCoefficientDistance P 0 A rho B sigma < eta →
      ∀ x : Base, (∀ alpha : SphereCotangent x,
        |B x alpha alpha-A x alpha alpha| ≤ eps*A x alpha alpha) ∧
        |sigma x-rho x| ≤ eps*rho x := by
  obtain ⟨m,hm,hmargin⟩ := sphere_finite_atlas_coercivity P A hA hs hp rho hr hrp
  refine ⟨eps*m,mul_pos heps hm,?_⟩
  intro B sigma hB hBs hBp hsig hdist x
  obtain ⟨p,hpP,z,hz,rfl⟩ := hcover x
  have hcmp := coefficient_relative_comparison (intrinsicChartCoefficient A rho p z)
    (intrinsicChartCoefficient B sigma p z) hm heps.le (hmargin p hpP z hz).1 (hmargin p hpP z hz).2
    ((sphereCoefficientDistance_value_bound P 0 A B rho sigma
      (fun p _ ↦ intrinsic_coefficient_chart_smooth A hA hs hp rho hr p)
      (fun p _ ↦ intrinsic_coefficient_chart_smooth B hB hBs hBp sigma hsig p) p hpP z hz).trans hdist.le)
  refine ⟨?_,hcmp.2⟩
  intro alpha
  let beta : BaseModel →L[ℝ] ℝ := alpha.comp
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z)
  have hrep : sphereCoordinateCovector p z (baseCovectorCoordinates beta) = alpha := by
    symm
    apply sphereCoordinateCovector_unique p (by rw [centeredSphereChart_target]; trivial)
    intro w
    change beta (WithLp.toLp 2 w) = _
    exact baseCovectorCoordinates_apply beta _
  have h := hcmp.1 beta
  rw [intrinsicChartCoefficient_pair B sigma,intrinsicChartCoefficient_pair A rho,hrep] at h
  exact h

end
end Yau.Target

end OAI
