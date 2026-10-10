import Mathlib
import OAI.Analysis.AffineBernstein.ParametricBasis

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

/- The actual graph area in an arbitrary smooth chart, with arbitrary inward
normalized conormal. This is a density identity, not a stationarity premise. -/
lemma graph_chart_parametricAreaDensity {n : ℕ} {Ω U : Set (Space n)}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {φ : Space n → Space n} (hφ : ContDiffOn ℝ ∞ φ U) (hφΩ : φ '' U ⊆ Ω)
    {x : Space n} (hx : x ∈ U) (hJ : (parametricJacobian φ x).det ≠ 0)
    (ν : (Space n × ℝ) →L[ℝ] ℝ) (ξ : Space n × ℝ)
    (hν : ν.comp (fderiv ℝ (fun y => (φ y,u (φ y))) x) = 0)
    (hξ : ν ξ = 1) (hc : 0 < ν ((0 : Space n),1)) :
    parametricAreaDensity (graphAmbientBasis n) (fun y => (φ y,u (φ y))) ν ξ x =
      |LinearMap.det (fderiv ℝ φ x).toLinearMap| * affineAreaDensity u (φ x) := by
  let L := ContinuousLinearEquiv.refl ℝ (Space n × ℝ)
  let β : Space n → ℝ := fun _ => 0
  let a : Fin n → Space n → ℝ := fun _ _ => 0
  have hβ : ContDiff ℝ ∞ β := contDiff_const
  have ha : ∀ k, ContDiff ℝ ∞ (a k) := fun _ => contDiff_const
  have hX : ((fun y => L (graphParamVariation u β a 0 y)+0) ∘ φ) =
      (fun y => (φ y,u (φ y))) := by funext y; simp [L,graphParamVariation]
  have hJ0 : (graphVariationJacobian a (0,φ x)).det ≠ 0 := by simp [graphVariationJacobian]
  have hH0 : 0 ≤ (graphVariationSecond u β a (0,φ x)).det := by
    simpa [graphVariationSecond] using (hp (φ x) (hφΩ (mem_image_of_mem φ hx))).det_pos.le
  have hh := coordinateAffineVariationArea_choices hΩ hU hu hβ ha L 0 hφ hφΩ hx hJ 0
    hJ0 hH0 ν ξ (by simpa only [hX] using hν) hξ (by simpa [L] using hc)
  rw [hX] at hh
  rw [hh,coordinateAffineVariationArea_eq hΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn) L 0 (hφ.contDiffAt (hU.mem_nhds hx))
    (hφΩ (mem_image_of_mem φ hx)) hJ 0 hJ0 hH0,
    affineParametricVariationArea_eq hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn)
      L 0 (hφΩ (mem_image_of_mem φ hx)) 0]
  have hdet : LinearMap.det L.toLinearEquiv.toLinearMap = 1 := by
    change LinearMap.det (LinearMap.id : (Space n × ℝ) →ₗ[ℝ] (Space n × ℝ)) = 1
    simp
  simp [hdet,graphVariationArea,variationAreaDensity,affineAreaDensity]

/- Exact local area transport for an arbitrary immersed parametrization of the
actual graph. The inverse chart is constructed, and all measurable subsets of
its source share the same determinant-normalized area identity. -/
theorem immersed_graph_local_area_transport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → E} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : E ≃L[ℝ] (Space n × ℝ))
    (him : ∀ y ∈ U, (a+L (X y)).1 ∈ Ω ∧ (a+L (X y)).2 = u (a+L (X y)).1)
    {x₀ : Space n} (hx₀ : x₀ ∈ U) (hi : Function.Injective (fderiv ℝ X x₀))
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) :
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n), x₀ ∈ φ.source ∧ φ.source ⊆ U ∧
      φ.target ⊆ Ω ∧ ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      (∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x))) ∧
      ∀ (K : Set (Space n)), MeasurableSet K → K ⊆ φ.source →
      ∀ (ν : Space n → E →L[ℝ] ℝ) (ξ : Space n → E),
      (∀ x ∈ K, (ν x).comp (fderiv ℝ X x) = 0) →
      (∀ x ∈ K, ν x (ξ x) = 1) →
      (∀ x ∈ K, 0 < ν x (L.symm ((0 : Space n),1))) →
      (∫ x in K, parametricAreaDensity b X (ν x) (ξ x) x) =
        Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n : ℝ)/((n : ℝ)+2)) * ∫ y in φ '' K, affineAreaDensity u y := by
  let Z : Space n → Space n × ℝ := fun y => a+L (X y)
  have hZ : ContDiffOn ℝ ∞ Z U := contDiffOn_const.add (L.contDiff.comp_contDiffOn hX)
  have hiZ : Function.Injective (fderiv ℝ Z x₀) := by
    have hd := ((L.hasFDerivAt.comp x₀
      ((hX.contDiffAt (hU.mem_nhds hx₀)).differentiableAt (by simp)).hasFDerivAt).const_add a).fderiv
    change fderiv ℝ Z x₀ = _ at hd
    rw [hd]
    exact L.injective.comp hi
  obtain ⟨φ,hxφ,hs,ht,he,hφ,hψ⟩ := exists_smooth_graph_chart hU hΩ hZ hu him hx₀ hiZ
  refine ⟨φ,hxφ,hs,ht,hφ,hψ,he,?_⟩
  intro K hK hKW ν ξ hν hξ hc
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
      ext w
      simpa using congrArg (fun T : Space n →L[ℝ] ℝ => T w) (hν x hx)
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
  change (∫ x in K, _) = c * _
  rw [setIntegral_congr_fun hK hpt,integral_const_mul]
  congr 1
  simpa only [smul_eq_mul] using
    (integral_image_eq_integral_abs_det_fderiv_smul volume hK
      (fun x hx => ((hφ.contDiffAt (φ.open_source.mem_nhds (hKW hx))).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt)
      (φ.injOn.mono hKW) (affineAreaDensity u)).symm

end AffineBernstein
end

end OAI
