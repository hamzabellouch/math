import OAI.Geometry.NodalSets.Spectral.SphereRayleighQuotient

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

def sphereChartFlux (A : IntrinsicTensor) (v : Base → ℝ) (p : Base) : Yau.Jets.Coord → Yau.Jets.Coord :=
  fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*Yau.coordPartial (v ∘ sphereChartCoordMap p) y j

theorem sphere_smooth_green_compact_chart (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base)
    (hc : HasCompactSupport (u ∘ sphereChartCoordMap p)) :
    Integrable (fun x ↦ roundCoordDensity x*(u (sphereChartCoordMap p x))*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) ∧
    sphereDirichletForm A u v = -(∫ x, roundCoordDensity x*(u (sphereChartCoordMap p x))*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) := by
  have h := Yau.compact_weighted_integration_by_parts roundCoordDensity
    (u ∘ sphereChartCoordMap p) roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
    (spherePullback_smooth u hu p) hc (sphereChartFlux A v p)
    (intrinsicRealVector_smooth A hA hs hp v hv p)
  refine ⟨h.2.1,?_⟩
  rw [sphereDirichletForm,sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  simpa only [Yau.pairing,sphereChartFlux,Function.comp_apply,Finset.mul_sum,mul_assoc] using h.2.2

theorem sphere_smooth_green_finite_partition (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ x, ∑ p, theta p x = 1) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) ∧
      ∀ u v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        sphereDirichletForm A u v = -(∑ p, ∫ x, roundCoordDensity x*
          (theta p (sphereChartCoordMap p.val x)*u (sphereChartCoordMap p.val x))*
          Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p.val) x) := by
  classical
  obtain ⟨P,theta,htheta,_,hsum,_,_,hcompact⟩ := sphere_finite_smooth_partition
  refine ⟨P,theta,htheta,hsum,hcompact,?_⟩
  intro u v hu hv
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ theta p x*u x
  have hf (p : {p // p ∈ P}) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f p) := (htheta p).mul hu
  have hsumf (x : Base) : ∑ p, f p x = u x := by
    simp only [f,← Finset.sum_mul,hsum,one_mul]
  have he (p : {p // p ∈ P}) :=
    (sphere_smooth_green_compact_chart A hA hs hp (f p) v (hf p) hv p.val ((hcompact p).mul_right)).2
  calc
    _ = ∫ x, ∑ p, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (sphere_differential_pair_finite_sum A f u v hf hu hv hsumf x).symm)
    _ = ∑ p, sphereDirichletForm A (f p) v :=
      integral_finsetSum _ (fun p _ ↦ intrinsic_differential_pair_integrable A hA hs hp (f p) v (hf p) hv)
    _ = _ := by simp only [he,Finset.sum_neg_distrib,f]

end
end Yau.Target

end OAI
