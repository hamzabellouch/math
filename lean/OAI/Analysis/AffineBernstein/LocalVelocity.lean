import Mathlib
import OAI.Analysis.AffineBernstein.ParametricChartStationarity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma contDiff_indicator_vector_of_compact {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    ContDiff ℝ ∞ (U.indicator f) ∧ tsupport (U.indicator f) ⊆ K := by
  have hs : Function.support (U.indicator f) ⊆ K := by
    intro x hx
    by_contra hxK
    by_cases hxU : x ∈ U
    · exact hx (by rw [Set.indicator_of_mem hxU,hz x hxU hxK])
    · exact hx (Set.indicator_of_notMem hxU f)
  have ht : tsupport (U.indicator f) ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨?_,ht⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (U.indicator f)
  · have hxU := hKU (ht hx)
    apply (hf.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact Set.indicator_of_mem hy f
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

/- Push a compactly supported smooth local velocity through a genuine smooth
coordinate inverse and extend by zero. Smoothness at the chart boundary is
proved, not an extra assumption on the transported velocity. -/
lemma smooth_local_velocity_transport {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : OpenPartialHomeomorph E F) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    {K : Set E} (hK : IsCompact K) (hKφ : K ⊆ φ.source)
    {V : E → G} (hV : ContDiffOn ℝ ∞ V φ.source) (hVK : tsupport V ⊆ K) :
    ∃ W : F → G, ContDiff ℝ ∞ W ∧ tsupport W ⊆ φ '' K ∧
      ∀ x ∈ φ.source, W (φ x) = V x := by
  let W := φ.target.indicator (V ∘ φ.symm)
  have hiK : IsCompact (φ '' K) := hK.image_of_continuousOn (φ.continuousOn.mono hKφ)
  have hit : φ '' K ⊆ φ.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact φ.map_source (hKφ hx)
  have hsm : ContDiffOn ℝ ∞ (V ∘ φ.symm) φ.target :=
    hV.comp hψ (fun y hy => φ.map_target hy)
  have hz : ∀ y ∈ φ.target, y ∉ φ '' K → (V ∘ φ.symm) y = 0 := by
    intro y hy hny
    change V (φ.symm y) = 0
    apply notMem_tsupport_iff_eventuallyEq.mp ?_ |>.self_of_nhds
    intro ht
    apply hny
    exact ⟨φ.symm y,hVK ht,φ.right_inv hy⟩
  obtain ⟨hW,hWK⟩ := contDiff_indicator_vector_of_compact φ.open_target hiK hit hsm hz
  refine ⟨W,hW,hWK,?_⟩
  intro x hx
  simp only [W,Set.indicator_of_mem (φ.map_source hx),Function.comp_apply,φ.left_inv hx]

lemma smooth_chart_jacobian_ne {n : ℕ} (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    {x : Space n} (hx : x ∈ φ.source) : (parametricJacobian φ x).det ≠ 0 := by
  have hd := ((hψ.contDiffAt (φ.open_target.mem_nhds (φ.map_source hx))).differentiableAt (by simp)).hasFDerivAt.comp x
    ((hφ.contDiffAt (φ.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have he : (φ.symm ∘ φ) =ᶠ[nhds x] id := by
    filter_upwards [φ.open_source.mem_nhds hx] with y hy
    exact φ.left_inv hy
  have hder : (fderiv ℝ φ.symm (φ x)).comp (fderiv ℝ φ x) = ContinuousLinearMap.id ℝ (Space n) := by
    rw [← hd.fderiv,he.fderiv_eq,fderiv_id]
  rw [parametricJacobian_det]
  have hdets := congrArg (fun A : Space n →L[ℝ] Space n => LinearMap.det A.toLinearMap) hder
  change LinearMap.det ((fderiv ℝ φ.symm (φ x)).toLinearMap.comp (fderiv ℝ φ x).toLinearMap) = _ at hdets
  rw [LinearMap.det_comp] at hdets
  have hone : LinearMap.det (ContinuousLinearMap.id ℝ (Space n)).toLinearMap = 1 := LinearMap.det_id
  rw [hone] at hdets
  exact right_ne_zero_of_mul_eq_one hdets

/- Every compact smooth ambient velocity in a local chart is a genuine
compact smooth graph velocity. This removes the extension requirement from
the coordinate stationarity theorem. -/
theorem affineMaximal_local_chart_stationary {n : ℕ}
    {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (hKφ : K ⊆ φ.source) (hφΩ : φ.target ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    {V : Space n → Space n × ℝ} (hV : ContDiffOn ℝ ∞ V φ.source)
    (hVK : tsupport V ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    ∃ (β : Space n → ℝ) (a : Fin n → Space n → ℝ),
      ContDiff ℝ ∞ β ∧ (∀ i, ContDiff ℝ ∞ (a i)) ∧
      tsupport β ⊆ φ '' K ∧ (∀ i, tsupport (a i) ⊆ φ '' K) ∧
      (∀ x ∈ φ.source, ∀ t : ℝ,
        L (graphParamVariation u β a t (φ x))+v =
          L (φ x,u (φ x))+v+t • V x) ∧
      HasDerivAt (fun t : ℝ => ∫ x in K,
        coordinateAffineVariationArea L v φ u β a x t) 0 0 := by
  obtain ⟨W,hW,hWK,hWe⟩ := smooth_local_velocity_transport φ hψ hK hKφ
    (L.symm.contDiff.comp_contDiffOn hV)
    ((tsupport_comp_subset (map_zero L.symm) V).trans hVK)
  let β : Space n → ℝ := fun x => (W x).2
  let a : Fin n → Space n → ℝ := fun i x => (W x).1 i
  have hβ : ContDiff ℝ ∞ β := hW.snd
  have ha (i : Fin n) : ContDiff ℝ ∞ (a i) :=
    (coordinateProjection n i).contDiff.comp hW.fst
  have hβK : tsupport β ⊆ φ '' K := (tsupport_comp_subset (g := Prod.snd) rfl W).trans hWK
  have haK (i : Fin n) : tsupport (a i) ⊆ φ '' K :=
    (tsupport_comp_subset (g := fun w : Space n × ℝ => w.1 i) rfl W).trans hWK
  refine ⟨β,a,hβ,ha,hβK,haK,?_,?_⟩
  · intro x hx t
    have he : (horizontalVelocity a (φ x),β (φ x)) = L.symm (V x) := by
      have hh := hWe x hx
      change W (φ x) = L.symm (V x) at hh
      rw [← hh]
      rfl
    have hs : graphParamVariation u β a t (φ x) =
        (φ x,u (φ x))+t • L.symm (V x) := by
      rw [← he]
      rfl
    rw [hs,map_add,map_smul,L.apply_symm_apply]
    abel
  · exact affineMaximal_coordinate_parametric_area_stationary hΩ hK
      (fun x hx => hφ.contDiffAt (φ.open_source.mem_nhds (hKφ hx)))
      (φ.injOn.mono hKφ) (fun x hx => smooth_chart_jacobian_ne φ hφ hψ (hKφ hx))
      (by rintro _ ⟨x,hx,rfl⟩; exact hφΩ (φ.map_source (hKφ hx)))
      hu hp hm hβ hβK ha haK L v

end AffineBernstein
end

end OAI
