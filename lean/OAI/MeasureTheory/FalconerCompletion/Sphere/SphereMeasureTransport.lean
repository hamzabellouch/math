import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.DiagonalBinMassLe
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereSupportedRapid

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
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

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real
open scoped ContDiff ComplexConjugate Topology
attribute [local instance] Classical.propDecidable

noncomputable def sphereAmbientEuclideanND (n : ℕ) :
    SphereAmbientND n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  ((stdOrthonormalBasis ℝ (SphereAmbientND n)).reindex
    (finCongr finrank_sphereAmbientND)).repr

theorem sphere_supported_rapid_euclideanND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (B T : ℝ) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (U W : Set (EuclideanSpace ℝ (Fin (n+1))))
        (b c : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (e z : EuclideanSpace ℝ (Fin (n+1))) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → ContDiff ℝ ∞ c →
      (∀ w∈U, -w∈U) → (∀ w∈W, -w∈W) → tsupport b ⊆ U → tsupport c ⊆ W →
      ‖e‖=1 → ‖z‖=1 →
      1≤A → A≤R^2 → 0<Λ → 0<Μ → A^2/Λ≤R^(-θ) → A^2/Μ≤R^(-θ) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j c w‖≤C*A^j) →
      R^B*‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖ ≤
        R^B*(if e∈U ∧ z∈W then H*(Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))/(1+|Λ-Μ|)^2 else 0)+R^(-T) := by
  obtain ⟨J,H,hH,hJ⟩ := sphere_supported_rapidND (n := n) hΨ hs C hC hθ B T
  refine ⟨J,H,hH,?_⟩
  let E := sphereAmbientEuclideanND n
  filter_upwards [hJ] with R hJ
  intro U W b c e z A Λ Μ hb hc hU hW hbU hcW he hz hA hAup hΛ hΜ hratΛ hratΜ hbd hcd
  have hpre (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (S : Set (EuclideanSpace ℝ (Fin (n+1))))
      (hf : tsupport f⊆S) : tsupport (f ∘ E)⊆E ⁻¹' S :=
    (tsupport_comp_subset_preimage f E.continuous).trans (preimage_mono hf)
  have hh := hJ (E ⁻¹' U) (E ⁻¹' W) (b ∘ E) (c ∘ E) (E.symm e) (E.symm z) A Λ Μ
    (hb.comp E.toContinuousLinearEquiv.contDiff) (hc.comp E.toContinuousLinearEquiv.contDiff)
    (by intro w hw; change E (-w)∈U; simpa only [map_neg] using hU (E w) hw)
    (by intro w hw; change E (-w)∈W; simpa only [map_neg] using hW (E w) hw)
    (hpre b U hbU) (hpre c W hcW) (by simpa using he) (by simpa using hz)
    hA hAup hΛ hΜ hratΛ hratΜ
    (by intro j hj w hw; rw [E.norm_iteratedFDeriv_comp_right]; exact hbd j hj (E w) (by simpa using hw))
    (by intro j hj w hw; rw [E.norm_iteratedFDeriv_comp_right]; exact hcd j hj (E w) (by simpa using hw))
  have hk (u : ℝ) : sphereAxisIntegralND (Λ*u) e b=sphereAxisIntegralND (Λ*u) (E.symm e) (b ∘ E) := by
    simpa using sphereAxisIntegralND_transport E (Λ*u) (E.symm e) b
  have hl (u : ℝ) : sphereAxisIntegralND (Μ*u) z c=sphereAxisIntegralND (Μ*u) (E.symm z) (c ∘ E) := by
    simpa using sphereAxisIntegralND_transport E (Μ*u) (E.symm z) c
  simp only [Set.mem_preimage,LinearIsometryEquiv.apply_symm_apply] at hh
  simpa only [hk,hl] using hh

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
