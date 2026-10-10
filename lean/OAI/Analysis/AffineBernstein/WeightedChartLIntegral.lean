import Mathlib
import OAI.Analysis.AffineBernstein.ActualChartArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

/- Weighted local area transport. The weight is any actual function on the
original graph; no integrability or measure transport premise is introduced. -/
theorem graph_chart_weighted_affineArea_lintegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → E} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : E ≃L[ℝ] (Space n × ℝ))
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hs : φ.source ⊆ U) (ht : φ.target ⊆ Ω)
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (he : ∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x)))
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKW : K ⊆ φ.source)
    (ν : Space n → E →L[ℝ] ℝ) (ξ : Space n → E)
    (hν : ∀ x ∈ K, (ν x).comp (fderiv ℝ X x) = 0)
    (hξ : ∀ x ∈ K, ν x (ξ x) = 1)
    (hc : ∀ x ∈ K, 0 < ν x (L.symm ((0 : Space n),1))) (w : Space n → ℝ≥0∞) :
    (∫⁻ x in K, ENNReal.ofReal (parametricAreaDensity b X (ν x) (ξ x) x) * w (φ x)) =
      ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
        ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y := by
  let Z : Space n → Space n × ℝ := fun y => a+L (X y)
  let b₀ := (graphAmbientBasis n).map L.symm.toLinearEquiv
  let c := Real.rpow |b.det b₀| ((n : ℝ)/((n : ℝ)+2))
  have hpt (x : Space n) (hx : x ∈ K) :
      parametricAreaDensity b X (ν x) (ξ x) x =
        c * (|LinearMap.det (fderiv ℝ φ x).toLinearMap| * affineAreaDensity u (φ x)) := by
    have hxU := hs (hKW hx)
    have hdX := (hX.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have heg : Z =ᶠ[nhds x] (fun y => (φ y,u (φ y))) := by
      filter_upwards [φ.open_source.mem_nhds (hKW hx)] with y hy
      exact he y hy
    have hdZ : fderiv ℝ Z x = L.toContinuousLinearMap.comp (fderiv ℝ X x) :=
      ((L.hasFDerivAt.comp x hdX.hasFDerivAt).const_add a).fderiv
    have hνZ : ((ν x).comp L.symm.toContinuousLinearMap).comp (fderiv ℝ Z x) = 0 := by
      rw [hdZ]
      ext v
      simpa using congrArg (fun T : Space n →L[ℝ] ℝ => T v) (hν x hx)
    rw [parametricAreaDensity_change_basis b₀ b]
    change c * parametricAreaDensity b₀ X (ν x) (ξ x) x = _
    congr 1
    rw [← parametricAreaDensity_volume_pullback (graphAmbientBasis n) L a hdX]
    change parametricAreaDensity (graphAmbientBasis n) Z _ _ x = _
    rw [parametricAreaDensity_congr (graphAmbientBasis n) heg]
    apply graph_chart_parametricAreaDensity hΩ φ.open_source hu hp hφ
      (by rintro _ ⟨y,hy,rfl⟩; exact ht (φ.map_source hy)) (hKW hx)
      (smooth_chart_jacobian_ne φ hφ hψ (hKW hx))
    · rw [← heg.fderiv_eq (𝕜 := ℝ)]
      exact hνZ
    · simpa using hξ x hx
    · exact hc x hx
  have hc : 0 ≤ c := Real.rpow_nonneg (abs_nonneg _) _
  change (∫⁻ x in K, _) = ENNReal.ofReal c * _
  calc
    _ = ∫⁻ x in K, ENNReal.ofReal c * (ENNReal.ofReal |LinearMap.det (fderiv ℝ φ x).toLinearMap| *
        (ENNReal.ofReal (affineAreaDensity u (φ x)) * w (φ x))) := by
      apply setLIntegral_congr_fun hK
      intro x hx
      dsimp only
      rw [hpt x hx,ENNReal.ofReal_mul hc,ENNReal.ofReal_mul (abs_nonneg _)]
      ring
    _ = ENNReal.ofReal c * ∫⁻ x in K, ENNReal.ofReal |LinearMap.det (fderiv ℝ φ x).toLinearMap| *
        (ENNReal.ofReal (affineAreaDensity u (φ x)) * w (φ x)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK
        (fun x hx => ((hφ.contDiffAt (φ.open_source.mem_nhds (hKW hx))).differentiableAt
          (by simp)).hasFDerivAt.hasFDerivWithinAt)
        (φ.injOn.mono hKW) (fun y => ENNReal.ofReal (affineAreaDensity u y) * w y)).symm

end AffineBernstein
end

end OAI
