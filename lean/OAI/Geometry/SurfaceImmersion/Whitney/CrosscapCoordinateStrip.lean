import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTransverseDerivative

namespace OAI

/-! The actual map on a rectangular source strip through two crosscaps,
with a nonzero transverse derivative along the entire central arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M}

structure CrosscapCoordinateStrip (A : CrosscapConnectingArc f p q) where
  chart : OpenPartialHomeomorph M Base
  width : ℝ
  width_pos : 0 < width
  chart_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ chart chart.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ chart.symm chart.target
  model : Base → ProjectionTarget 3
  model_smooth : ContDiff ℝ ∞ model
  domain : Set Base
  domain_open : IsOpen domain
  domain_target : domain ⊆ chart.target
  model_eq : EqOn model (f ∘ chart.symm) domain
  axis : ∀ t ∈ Icc A.arc.start A.arc.finish,
    A.arc.curve t ∈ chart.source ∧ chart (A.arc.curve t) = ![0,t]
  rectangle : ∀ x ∈ Icc (-width) width,
    ∀ t ∈ Icc (A.arc.start-width) (A.arc.finish+width), (![x,t] : Base) ∈ domain
  transverse : ∀ t ∈ Icc A.arc.start A.arc.finish,
    fderiv ℝ model (![0,t] : Base) (![1,0] : Base) ≠ 0
  interior_regular : ∀ t ∈ Ioo A.arc.start A.arc.finish,
    Function.Injective (fderiv ℝ model (![0,t] : Base))
  left_vertical : fderiv ℝ model (![0,A.arc.start] : Base) (![0,1] : Base) = 0
  right_vertical : fderiv ℝ model (![0,A.arc.finish] : Base) (![0,1] : Base) = 0

theorem exists_crosscap_coordinate_strip
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (A : CrosscapConnectingArc f p q) : Nonempty (CrosscapCoordinateStrip A) := by
  obtain ⟨c,δ,φ,U,hδ,hcs,hci,hφ,hU,hUt,hEq,haxis,hrect⟩ := source_map_representative A.arc hf
  have hUaxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U := by
    intro t ht
    apply hrect 0 ⟨by linarith,by linarith⟩ t
    constructor <;> linarith [ht.1,ht.2]
  have hrecover : ∀ t ∈ Icc A.arc.start A.arc.finish, c.symm (![0,t] : Base) = A.arc.curve t := by
    intro t ht
    rw [← (haxis t ht).2,c.left_inv (haxis t ht).1]
  have hleft : fderiv ℝ φ (![0,A.arc.start] : Base) (![0,1] : Base) = 0 :=
    (coordinate_axis_derivative A.arc c hf hφ hEq haxis hUaxis
      (left_mem_Icc.mpr A.arc.start_lt_finish.le)).trans A.endpoint_image_velocity.1
  have hright : fderiv ℝ φ (![0,A.arc.finish] : Base) (![0,1] : Base) = 0 :=
    (coordinate_axis_derivative A.arc c hf hφ hEq haxis hUaxis
      (right_mem_Icc.mpr A.arc.start_lt_finish.le)).trans A.endpoint_image_velocity.2
  have hregular : ∀ t ∈ Ioo A.arc.start A.arc.finish,
      Function.Injective (fderiv ℝ φ (![0,t] : Base)) := by
    intro t ht
    apply (coordinate_representative_immersion_iff c hcs hci hf hU hUt hEq (hUaxis t ⟨ht.1.le,ht.2.le⟩)).mpr
    rw [hrecover t ⟨ht.1.le,ht.2.le⟩]
    exact A.regular t ht
  refine ⟨⟨c,δ,hδ,hcs,hci,φ,hφ,U,hU,hUt,hEq,haxis,hrect,?_,hregular,hleft,hright⟩⟩
  intro t ht
  by_cases hl : t = A.arc.start
  · subst t
    apply horizontal_ne_zero_of_vertical_zero _ ?_ hleft
    apply coordinate_representative_derivative_ne_zero c hcs hci hf hU hUt hEq (hUaxis _ ht)
    rw [hrecover _ ht,A.source]
    exact A.left.derivative_ne_zero hf
  · by_cases hr : t = A.arc.finish
    · subst t
      apply horizontal_ne_zero_of_vertical_zero _ ?_ hright
      apply coordinate_representative_derivative_ne_zero c hcs hci hf hU hUt hEq (hUaxis _ ht)
      rw [hrecover _ ht,A.target]
      exact A.right.derivative_ne_zero hf
    · have hreg := hregular t ⟨lt_of_le_of_ne ht.1 (Ne.symm hl),lt_of_le_of_ne ht.2 hr⟩
      intro hz
      have hh := hreg (hz.trans (map_zero _).symm)
      have h0 := congrFun hh 0
      norm_num at h0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
