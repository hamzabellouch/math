import OAI.Geometry.NodalSets.Charts.SphereChartScalarExtension
import OAI.Geometry.NodalSets.Charts.SphereSmoothGreenLocal
import OAI.Geometry.NodalSets.Elliptic.CompactFluxGreen

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

theorem sphereChartFlux_hasCompactSupport (A : IntrinsicTensor) (v : Base → ℝ) (p : Base)
    (hc : HasCompactSupport (v ∘ sphereChartCoordMap p)) (i : Fin 4) :
    HasCompactSupport (fun x ↦ sphereChartFlux A v p x i) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
    (hc.fderiv_apply ℝ (Pi.single j 1)).mul_left
      (f := fun x ↦ intrinsicRealPrincipal A p x i j))
  convert h using 1
  rfl

theorem sphere_smooth_green_compact_flux (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base)
    (hc : HasCompactSupport (v ∘ sphereChartCoordMap p)) :
    Integrable (fun x ↦ roundCoordDensity x*u (sphereChartCoordMap p x)*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) ∧
    sphereDirichletForm A u v = -(∫ x, roundCoordDensity x*u (sphereChartCoordMap p x)*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) := by
  have h := Yau.compact_flux_weighted_integration_by_parts roundCoordDensity
    (u ∘ sphereChartCoordMap p) roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
    (spherePullback_smooth u hu p) (sphereChartFlux A v p)
    (intrinsicRealVector_smooth A hA hs hp v hv p) (sphereChartFlux_hasCompactSupport A v p hc)
  refine ⟨h.2.1,?_⟩
  rw [sphereDirichletForm,sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  simpa only [Yau.pairing,sphereChartFlux,Function.comp_apply,Finset.mul_sum,mul_assoc] using h.2.2

theorem sphere_compact_test_divergence_extension (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) :
    ∃ v g : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ g ∧
      (∀ x, v (sphereChartCoordMap p x) = phi x) ∧
      (∀ x, g (sphereChartCoordMap p x) = Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*Yau.coordPartial phi y j) x) ∧
      ∀ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u →
        sphereDirichletForm A u v = -(∫ x, u x*g x ∂sphereReferenceMeasure) := by
  obtain ⟨v,hv,_,hval⟩ := sphere_chart_scalar_extension p phi hphi hc
  have hcomp : v ∘ sphereChartCoordMap p = phi := funext hval
  have hvc : HasCompactSupport (v ∘ sphereChartCoordMap p) := hcomp ▸ hc
  let D := Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p)
  have hD : ContDiff ℝ ∞ D := Yau.weightedDiv_smooth roundCoordDensity_smooth
    (fun x ↦ (roundCoordDensity_pos x).ne') (intrinsicRealVector_smooth A hA hs hp v hv p)
  have hDc : HasCompactSupport D := Yau.weightedDiv_hasCompactSupport _ _
    (sphereChartFlux_hasCompactSupport A v p hvc)
  obtain ⟨g,hg,_,hgval⟩ := sphere_chart_scalar_extension p D hD hDc
  refine ⟨v,g,hv,hg,hval,?_,?_⟩
  · intro x
    rw [hgval]
    change Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x = _
    have hflux : sphereChartFlux A v p =
        (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*Yau.coordPartial phi y j) := by
      unfold sphereChartFlux
      rw [hcomp]
    rw [hflux]
  · intro u hu
    rw [(sphere_smooth_green_compact_flux A hA hs hp u v hu hv p hvc).2,
      sphereReferenceMeasure_integral_chart p]
    simp only [roundChartDensity_coord_eq,hgval,D,mul_assoc]

end
end Yau.Target

end OAI
