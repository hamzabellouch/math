import OAI.Geometry.SurfaceImmersion.Whitney.ActualRuledCrosscapStrip
import OAI.Geometry.SurfaceImmersion.Geometry.CompactVaryingFrameTube
import OAI.Geometry.SurfaceImmersion.Whitney.RulingLinearTarget

namespace OAI

/-! The constructed surface contains a genuine framed target tube on
 its ruled inner rectangle, with uniformly invertible differential. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}
variable {S : CrosscapCoordinateStrip A} {c d : ℝ}

theorem ActualRuledRectangle.target_tube (R : ActualRuledRectangle S c d)
    (hac : A.arc.start < c) (hcd : c ≤ d) (hdb : d < A.arc.finish) :
    ∃ (T : Base × ℝ → Fin 3 → ℝ) (r : ℝ) (U : Set ℝ),
      ContDiff ℝ ∞ T ∧ 0 < r ∧ IsOpen U ∧ Icc c d ⊆ U ∧
      (∀ x : Base, ‖x‖ < r → ∀ t ∈ U, Function.Bijective (fderiv ℝ T (x,t))) ∧
      ∀ x : ℝ, |x| < r → ∀ t ∈ Icc c d,
        T (![x,0],t) = EuclideanSpace.equiv (Fin 3) ℝ (R.model ![x,t]) := by
  let E := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  let F : Base → Fin 3 → ℝ := E ∘ S.model
  have hF : ContDiff ℝ ∞ F := E.contDiff.comp S.model_smooth
  have hI : ∀ t ∈ Icc c d, Function.Injective (fderiv ℝ F (crosscapAxis t)) := by
    intro t ht
    have htab : t ∈ Ioo A.arc.start A.arc.finish :=
      ⟨hac.trans_le ht.1,ht.2.trans_lt hdb⟩
    dsimp only [F]
    rw [fderiv_comp _ E.differentiableAt (S.model_smooth.differentiable (by simp) _),E.fderiv]
    have hbase : Function.Injective (fderiv ℝ S.model (crosscapAxis t)) := by
      simpa only [crosscapAxis_apply] using S.interior_regular t htab
    intro u v huv
    apply hbase
    exact (EuclideanSpace.equiv (Fin 3) ℝ).injective huv
  let T := varyingFramedCurveTube (axisValue F) (axisTransverse F)
  have hT : ContDiff ℝ ∞ T := varyingFramedCurveTube_smooth
    (axisValue_smooth hF) (axisTransverse_smooth hF)
  obtain ⟨ρ,U,hρ,hU,hKU,hTI⟩ := compact_varying_frame_tube
    (axisValue_smooth hF) (axisTransverse_smooth hF) isCompact_Icc
    (nonempty_Icc.mpr hcd) (fun t ht => (regular_axis_transverse hF (hI t ht)).1)
    (fun t ht => (regular_axis_transverse hF (hI t ht)).2)
  refine ⟨T,min ρ R.radius,U,hT,lt_min hρ R.radius_pos,hU,hKU,?_,?_⟩
  · intro x hx t ht
    exact hTI x (hx.trans_le (min_le_left _ _)) t ht
  · intro x hx t ht
    have hxr : |x| ≤ R.radius := (hx.trans_le (min_le_right _ _)).le
    have htr : t ∈ Icc (c-R.radius) (d+R.radius) :=
      ⟨by linarith [ht.1,R.radius_pos],by linarith [ht.2,R.radius_pos]⟩
    have he := (R.ruled_rectangle x (abs_le.mp hxr) t htr).2
    change varyingFramedCurveTube (axisValue F) (axisTransverse F) (![x,0],t) = E (R.model ![x,t])
    rw [varyingFramedCurveTube_zero_normal,he]
    exact ruling_linear_target E S.model_smooth ![x,t]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
