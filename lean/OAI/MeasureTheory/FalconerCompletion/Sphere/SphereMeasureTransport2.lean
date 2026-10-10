import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularOperator2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereInverseArbitraryPower
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasureTransport

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ENNReal Pointwise ContDiff Topology RealInnerProductSpace
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

lemma canonicalSphereMeasureND_transport (e : V ≃ₗᵢ[ℝ] W) :
    MeasurePreserving e (canonicalSphereMeasureND V) (canonicalSphereMeasureND W) := by
  refine ⟨e.continuous.measurable,?_⟩
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    canonicalSphereMeasureND_apply (e.continuous.measurable hs),canonicalSphereMeasureND_apply hs,
    e.toLinearEquiv.finrank_eq]
  congr 1
  have hset : Ioo (0:ℝ) 1 • (sphere (0:V) 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Ioo (0:ℝ) 1 • (sphere (0:W) 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,w,⟨hw,hsw⟩,rfl⟩
      exact ⟨r,hr,e w,⟨by simpa using hw,hsw⟩,by simp⟩
    · rintro ⟨r,hr,w,⟨hw,hsw⟩,hwx⟩
      refine ⟨r,hr,e.symm w,⟨by simpa using hw,by simpa using hsw⟩,?_⟩
      apply e.injective
      simpa using hwx
  rw [hset,e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

lemma integral_canonicalSphereMeasureND_transport (e : V ≃ₗᵢ[ℝ] W) (f : W → ℂ) :
    (∫ w, f (e w) ∂canonicalSphereMeasureND V) = ∫ w, f w ∂canonicalSphereMeasureND W :=
  (canonicalSphereMeasureND_transport e).integral_comp e.toHomeomorph.measurableEmbedding f

lemma sphereAxisIntegralND_transport (e : V ≃ₗᵢ[ℝ] W) (Λ : ℝ) (v : V) (b : W → ℂ) :
    sphereAxisIntegralND Λ (e v) b = sphereAxisIntegralND Λ v (b ∘ e) := by
  unfold sphereAxisIntegralND
  rw [← integral_canonicalSphereMeasureND_transport e]
  simp only [LinearIsometryEquiv.inner_map_map,Function.comp_def]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
noncomputable def smoothPullND (e : V ≃ₗᵢ[ℝ] W) (f : SmoothFunctionND W) : SmoothFunctionND V :=
  ⟨f.1 ∘ e,(smoothFunctionND_contDiff f).comp e.toContinuousLinearEquiv.contDiff⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
lemma smoothPullND_derivative_norm (e : V ≃ₗᵢ[ℝ] W) (f : SmoothFunctionND W) (j : ℕ) (w : V) :
    ‖iteratedFDeriv ℝ j (smoothPullND e f).1 w‖ = ‖iteratedFDeriv ℝ j f.1 (e w)‖ :=
  e.norm_iteratedFDeriv_comp_right f.1 w j

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open scoped ContDiff Topology
variable {n : ℕ}

noncomputable def sphereEuclideanIsoND (n : ℕ) :
    SphereAmbientND n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  ((sphereBasisND n).reindex (finCongr finrank_sphereAmbientND)).repr

noncomputable def euclideanSphereBND (j : ℕ) (f : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) :=
  smoothPullND (sphereEuclideanIsoND n).symm (sphereBND j (smoothPullND (sphereEuclideanIsoND n) f))

lemma euclideanSphereBND_pull (j : ℕ) (f : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (w : SphereAmbientND n) :
    (euclideanSphereBND j f).1 (sphereEuclideanIsoND n w) =
      (sphereBND j (smoothPullND (sphereEuclideanIsoND n) f)).1 w := by
  simp only [euclideanSphereBND,smoothPullND,Function.comp_def,LinearIsometryEquiv.symm_apply_apply]

lemma euclideanSphereAxisBND (j : ℕ) (f : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Λ : ℝ) (v : EuclideanSpace ℝ (Fin (n+1))) :
    sphereAxisIntegralND Λ ((sphereEuclideanIsoND n).symm v)
      (fun w => ψ (sphereEuclideanIsoND n w)*(sphereBND j (smoothPullND (sphereEuclideanIsoND n) f)).1 w) =
    sphereAxisIntegralND Λ v (fun w => ψ w*(euclideanSphereBND j f).1 w) := by
  simpa only [LinearIsometryEquiv.apply_symm_apply,Function.comp_def,
    euclideanSphereBND_pull] using
    (sphereAxisIntegralND_transport (sphereEuclideanIsoND n) Λ
      ((sphereEuclideanIsoND n).symm v)
      (fun w => ψ w * (euclideanSphereBND j f).1 w)).symm

theorem euclidean_sphere_inverseND (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (κ T C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∃ E : ℝ, 0 ≤ E ∧ ∀ (b : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
      (R A Λ : ℝ) (v : EuclideanSpace ℝ (Fin (n+1))),
      1 ≤ R → 1 ≤ A → R^κ ≤ Λ → A ≤ R^2 → A^2/Λ ≤ R^(-κ) → ‖v‖=1 →
      ψ =ᶠ[𝓝 v] (fun _ => 1) → ψ =ᶠ[𝓝 (-v)] (fun _ => 0) →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ‖Complex.exp (Complex.I*Λ)*b.1 v -
        ((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND Λ v (fun w => ψ w*(euclideanSphereBND j b).1 w))‖ ≤ E*R^(-T) := by
  let Q := sphereEuclideanIsoND n
  have hψQ : ContDiff ℝ ∞ (ψ ∘ Q) := hψ.comp Q.toContinuousLinearEquiv.contDiff
  obtain ⟨J,E,hE,hEb⟩ := sphere_inverse_fixed_arbitrary_powerND (ψ ∘ Q) hψQ κ T C hκ hC
  refine ⟨J,E,hE,?_⟩
  intro b R A Λ v hR hA hΛ hup hratio hv hplus hminus hb
  have hp : (ψ ∘ Q) =ᶠ[𝓝 (Q.symm v)] (fun _ => 1) := by
    apply hplus.comp_tendsto
    simpa only [Q.apply_symm_apply] using Q.continuous.tendsto (Q.symm v)
  have hm : (ψ ∘ Q) =ᶠ[𝓝 (-Q.symm v)] (fun _ => 0) := by
    apply hminus.comp_tendsto
    simpa only [map_neg,Q.apply_symm_apply] using Q.continuous.tendsto (-Q.symm v)
  have hh := hEb (smoothPullND Q b) R A Λ (Q.symm v) hR hA hΛ hup hratio
    (by simpa using hv) hp hm (fun k hk w hw => by
      rw [smoothPullND_derivative_norm]
      exact hb k hk (Q w) (by simpa using hw))
  simp only [Function.comp_def] at hh
  have heval : (smoothPullND Q b).1 (Q.symm v) = b.1 v := by
    simp only [smoothPullND,Function.comp_def,Q.apply_symm_apply]
  rw [heval] at hh
  simpa only [Q,euclideanSphereAxisBND] using hh

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
