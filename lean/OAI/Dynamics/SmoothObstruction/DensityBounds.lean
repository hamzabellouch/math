import OAI.Dynamics.SmoothObstruction.Models

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.JacobianDomination
open MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Change of variables on the retained set itself. A density lower bound
on the actual Jacobian gives domination without normalizing the retained
measure. Global injectivity is essential here. -/
theorem map_density_restrict_le (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (d : E → ℝ≥0∞) (s : Set E) (hs : MeasurableSet s)
    (f : E → E) (hf : Measurable f) (J : E → E →L[ℝ] E)
    (hJ : ∀ x∈s,HasFDerivWithinAt f (J x) s x) (hinj : InjOn f s)
    (C : ℝ≥0∞) (hC : C≠∞)
    (hlower : ∀ x∈s,d x ≤ C*(ENNReal.ofReal |(J x).det| *d (f x))) :
    ((μ.withDensity d).restrict s).map f ≤ C • μ.withDensity d := by
  apply Measure.le_iff.mpr
  intro t ht
  rw [Measure.map_apply hf ht,Measure.restrict_apply (hf ht),
    withDensity_apply _ ((hf ht).inter hs),Measure.smul_apply,
    withDensity_apply _ ht,smul_eq_mul]
  let a := f ⁻¹' t ∩ s
  have ha : MeasurableSet a := (hf ht).inter hs
  have hsub : f '' a ⊆ t := by rintro y ⟨x,hx,rfl⟩; exact hx.1
  calc
    (∫⁻ x in a,d x ∂μ) ≤ ∫⁻ x in a,C*(ENNReal.ofReal |(J x).det| *d (f x)) ∂μ := by
      apply setLIntegral_mono' ha
      intro x hx
      exact hlower x hx.2
    _ = C*(∫⁻ x in a,ENNReal.ofReal |(J x).det| *d (f x) ∂μ) :=
      lintegral_const_mul' C _ hC
    _ = C*(∫⁻ y in f '' a,d y ∂μ) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ha
        (fun x hx => (hJ x hx.2).mono inter_subset_right) (hinj.mono inter_subset_right)]
    _ ≤ C*(∫⁻ y in t,d y ∂μ) := by
      gcongr

end SmoothObstruction.JacobianDomination

namespace SmoothObstruction.JacobianDomination
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Agreement with genuine local derivative branches on relative retained
neighborhoods gives a measurable total extension and the original retained-law
domination. The within-set change-of-variables theorem avoids any assumption
of measurable frame witnesses or measurable choices of local branches. -/
theorem local_branches_domination (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (d : E → ℝ≥0∞) (s : Set E) (hs : MeasurableSet s)
    (f : E → E) (J : E → E →L[ℝ] E)
    (hlocal : ∀ x∈s,∃ g : E → E,HasFDerivAt g (J x) x ∧ g =ᶠ[𝓝[s] x] f)
    (hinj : InjOn f s) (C : ℝ≥0∞) (hC : C≠∞)
    (hlower : ∀ x∈s,d x≤C*(ENNReal.ofReal |(J x).det| *d (f x))) :
    ∃ F : E → E,Measurable F ∧ EqOn F f s ∧
      ((μ.withDensity d).restrict s).map F≤C • μ.withDensity d := by
  classical
  have hder : ∀ x∈s,HasFDerivWithinAt f (J x) s x := by
    intro x hx
    obtain ⟨g,hg,he⟩ := hlocal x hx
    exact hg.hasFDerivWithinAt.congr_of_eventuallyEq he.symm (he.eq_of_nhdsWithin hx).symm
  have hc : ContinuousOn f s := fun x hx => (hder x hx).continuousWithinAt
  let F := s.piecewise f (fun _ => 0)
  have hF : Measurable F := hc.measurable_piecewise continuous_const.continuousOn hs
  have he : EqOn F f s := fun x hx => ite_eq_left hx
  refine ⟨F,hF,he,map_density_restrict_le μ d s hs F hF J
    (fun x hx => (hder x hx).congr' he hx) (hinj.congr he.symm) C hC ?_⟩
  intro x hx
  rw [he hx]
  exact hlower x hx
end SmoothObstruction.JacobianDomination

namespace SmoothObstruction.ChartDomination
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The image of a measurable carrier under a measurable coordinate map with
measurable inverse. Unlike an arbitrary image, this is visibly measurable. -/
def coordinateSet (e : X → E) (r : E → X) (G : Set X) : Set E :=
  {u | r u ∈ G ∧ e (r u) = u}

lemma measurable_coordinateSet (e : X → E) (r : E → X)
    (he : Measurable e) (hr : Measurable r) (G : Set X) (hG : MeasurableSet G) :
    MeasurableSet (coordinateSet e r G) :=
  (hG.preimage hr).inter (measurableSet_eq_fun (he.comp hr) measurable_id)

omit [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma coordinateSet_eq_image (e : X → E) (r : E → X) (G : Set X)
    (hleft : ∀ x ∈ G, r (e x) = x) : coordinateSet e r G = e '' G := by
  ext u
  constructor
  · rintro ⟨hu,heq⟩
    exact ⟨r u,hu,heq⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨by rwa [hleft x hx],congrArg e (hleft x hx)⟩

/-- Restricting an ORIGINAL measure before taking chart coordinates is
exactly restriction to the coordinate image, not conditioning on it. The
chart inverse is required only on the full original carrier Q. -/
theorem map_restrict_coordinateSet (μ : Measure X)
    (Q G : Set X) (hQ : μ Qᶜ = 0)
    (e : X → E) (r : E → X) (he : Measurable e) (hr : Measurable r)
    (hG : MeasurableSet G) (hleft : ∀ x ∈ Q, r (e x) = x) :
    (μ.restrict G).map e = (μ.map e).restrict (coordinateSet e r G) := by
  have hs := measurable_coordinateSet e r he hr G hG
  have hsets : G =ᵐ[μ] e ⁻¹' coordinateSet e r G := by
    filter_upwards [show ∀ᵐ x ∂μ,x∈Q from hQ] with x hx
    apply propext
    change (x∈G ↔ r (e x)∈G ∧ e (r (e x))=e x)
    rw [hleft x hx]
    simp
  rw [Measure.restrict_congr_set hsets]
  exact (Measure.restrict_map he hs).symm

/-- A local coordinate change transfers a genuine retained-set smooth branch
estimate back to the original measure. This provides a measurable extension
in the original space without an assumed globally measurable frame choice.
No retained mass is normalized, and the original carrier may be only Borel. -/
theorem local_domination (μ : Measure X) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (d : E → ℝ≥0∞)
    (Q G : Set X) (hQ : μ Qᶜ = 0) (hGQ : G ⊆ Q) (hG : MeasurableSet G)
    (e : X → E) (r : E → X) (he : Measurable e) (hr : Measurable r)
    (hleft : ∀ x∈Q,r (e x)=x) (hcoords : μ.map e=m.withDensity d)
    (f : X → X) (hfQ : MapsTo f G Q)
    (φ : E → E) (J : E → E →L[ℝ] E)
    (hcompat : ∀ x∈G,φ (e x)=e (f x))
    (hlocal : ∀ u∈coordinateSet e r G,
      ∃ g : E → E, HasFDerivAt g (J u) u ∧
        g =ᶠ[𝓝[coordinateSet e r G] u] φ)
    (hinj : InjOn φ (coordinateSet e r G)) (C : ℝ≥0∞) (hC : C≠∞)
    (hlower : ∀ u∈coordinateSet e r G,
      d u≤C*(ENNReal.ofReal |(J u).det| * d (φ u))) :
    ∃ F : X → X,Measurable F ∧ EqOn F f G ∧
      (μ.restrict G).map F≤C • μ := by
  have hs := measurable_coordinateSet e r he hr G hG
  obtain ⟨ψ,hψ,hψφ,hdom⟩ := JacobianDomination.local_branches_domination
    m d (coordinateSet e r G) hs φ J hlocal hinj C hC hlower
  let F : X → X := r ∘ ψ ∘ e
  have hF : Measurable F := hr.comp (hψ.comp he)
  have hrecover : (μ.map e).map r=μ := by
    rw [Measure.map_map hr he]
    have hh : r ∘ e =ᵐ[μ] id := by
      filter_upwards [show ∀ᵐ x ∂μ,x∈Q from hQ] with x hx
      exact hleft x hx
    rw [Measure.map_congr hh,Measure.map_id]
  refine ⟨F,hF,?_,?_⟩
  · intro x hx
    have hx' : e x∈coordinateSet e r G := by
      rw [coordinateSet_eq_image e r G (fun y hy => hleft y (hGQ hy))]
      exact mem_image_of_mem e hx
    change r (ψ (e x))=f x
    rw [hψφ hx',hcompat x hx,hleft (f x) (hfQ hx)]
  · have h := Measure.map_mono hdom hr
    rw [←hcoords,Measure.map_smul C hr.aemeasurable,hrecover] at h
    rw [←map_restrict_coordinateSet μ Q G hQ e r he hr hG hleft] at h
    simpa only [Measure.map_map hr hψ,Measure.map_map (hr.comp hψ) he,
      Function.comp_assoc,F] using h
end SmoothObstruction.ChartDomination

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Filter Topology
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma measurable_target (hclosed : IsClosed (range I)) (a : M) :
    MeasurableSet (extChartAt I a).target := by
  rw [extChartAt_target]
  exact ((chartAt H a).open_target.preimage I.continuous_symm).measurableSet.inter
    hclosed.measurableSet

noncomputable def coordinates (a : M) : M → EuclideanSpace ℝ (Fin d) := by
  classical
  exact (extChartAt I a).source.piecewise (extChartAt I a) (fun _ => 0)

noncomputable def inverse (a : M) : EuclideanSpace ℝ (Fin d) → M := by
  classical
  exact (extChartAt I a).target.piecewise (extChartAt I a).symm (fun _ => a)

lemma measurable_coordinates (a : M) : Measurable (coordinates I a) := by
  classical
  exact (continuousOn_extChartAt a).measurable_piecewise continuous_const.continuousOn
    (by rw [extChartAt_source]; exact (chartAt H a).open_source.measurableSet)

lemma measurable_inverse (hclosed : IsClosed (range I)) (a : M) :
    Measurable (inverse I a) := by
  classical
  exact (continuousOn_extChartAt_symm a).measurable_piecewise
    continuous_const.continuousOn (measurable_target I hclosed a)

omit [MeasurableSpace M] [BorelSpace M] in
lemma coordinates_eq (a x : M) (hx : x∈(extChartAt I a).source) :
    coordinates I a x=extChartAt I a x := by
  classical
  exact ite_eq_left hx

omit [MeasurableSpace M] [BorelSpace M] in
lemma inverse_eq (a : M) (u : EuclideanSpace ℝ (Fin d))
    (hu : u∈(extChartAt I a).target) : inverse I a u=(extChartAt I a).symm u := by
  classical
  exact ite_eq_left hu

omit [MeasurableSpace M] [BorelSpace M] in
lemma inverse_coordinates (a x : M) (hx : x∈(extChartAt I a).source) :
    inverse I a (coordinates I a x)=x := by
  rw [coordinates_eq I a x hx,inverse_eq I a _ ((extChartAt I a).map_source hx)]
  exact (extChartAt I a).left_inv hx

/-- Coordinates for each ORIGINAL measurable subcell carry precisely its chart
Lebesgue density, without conditioning on the cell or on a good set. All maps
have measurable total extensions; their arbitrary values off the chart are
irrelevant to the equality. -/
theorem cell_density (hclosed : IsClosed (range I)) (μ : Measure M)
    (hμ : SmoothPositiveDensity I μ) (a : M) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiffOn ℝ ∞ f (extChartAt I a).target ∧
      (∀ u∈(extChartAt I a).target,0<f u) ∧
      ∀ Q : Set M,MeasurableSet Q → Q⊆(extChartAt I a).source →
        let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
        Measurable (W.indicator (fun u => ENNReal.ofReal (f u))) ∧
        (μ.restrict Q).map (coordinates I a)=
          volume.withDensity (W.indicator (fun u => ENNReal.ofReal (f u))) := by
  classical
  obtain ⟨f,hf,hpos,hmap⟩ := hμ a
  refine ⟨f,hf,hpos,fun Q hQ hQsrc => ?_⟩
  let e := coordinates I a
  let r := inverse I a
  let V := (extChartAt I a).target
  let U := (extChartAt I a).source
  let W := ChartDomination.coordinateSet e r Q
  have he : Measurable e := measurable_coordinates I a
  have hr : Measurable r := measurable_inverse I hclosed a
  have hV : MeasurableSet V := measurable_target I hclosed a
  have hU : MeasurableSet U := by
    rw [show U=(chartAt H a).source from extChartAt_source I a]
    exact (chartAt H a).open_source.measurableSet
  have hW : MeasurableSet W := ChartDomination.measurable_coordinateSet e r he hr Q hQ
  have himage : W=e '' Q := ChartDomination.coordinateSet_eq_image e r Q
    (fun x hx => inverse_coordinates I a x (hQsrc hx))
  have hWV : W⊆V := by
    rw [himage]
    rintro u ⟨x,hx,rfl⟩
    rw [show e x=extChartAt I a x from coordinates_eq I a x (hQsrc hx)]
    exact (extChartAt I a).map_source (hQsrc hx)
  have hd : Measurable (W.indicator (fun u => ENNReal.ofReal (f u))) := by
    have hh : Measurable (W.piecewise f (fun _ => (0:ℝ))) :=
      (hf.continuousOn.mono hWV).measurable_piecewise
        continuous_const.continuousOn hW
    have hh' := hh.ennreal_ofReal
    convert hh' using 1
    funext u
    by_cases hu : u∈W <;> simp [Set.indicator,Set.piecewise,hu]
  refine ⟨hd,?_⟩
  have hemap : (μ.restrict U).map e=(volume.withDensity (fun u => ENNReal.ofReal (f u))).restrict V := by
    rw [←hmap]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hU] with x hx
    exact coordinates_eq I a x hx
  have hfull : (μ.restrict U) Uᶜ=0 := by
    rw [Measure.restrict_apply hU.compl,compl_inter_self,measure_empty]
  have hm := ChartDomination.map_restrict_coordinateSet (μ.restrict U) U Q hfull
    e r he hr hQ (fun x hx => inverse_coordinates I a x hx)
  rw [Measure.restrict_restrict hQ,inter_eq_left.mpr hQsrc,hemap,
    Measure.restrict_restrict hW,inter_eq_left.mpr hWV] at hm
  rw [hm,restrict_withDensity hW,←withDensity_indicator hW]
end SmoothObstruction.ChartDensity

end

end OAI
