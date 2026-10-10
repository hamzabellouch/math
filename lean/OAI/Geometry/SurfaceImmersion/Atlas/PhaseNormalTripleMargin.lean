import OAI.Geometry.SurfaceImmersion.Atlas.RealPhaseChart
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartNormalTransport
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveNormalCoordinates

namespace OAI

/-! The normal triple of the actual inverse-chart map controls the old
coordinate immersion and second form with a fixed compact-chart constant. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetVelocityCoordinates SurfaceVelocityFamily.Loop SurfaceJetCoordinates RealModes

lemma normalTriple_secondTensor_margin {F : SmallModes.Base → RealModes.RVec 4}
    (hF : ContDiff ℝ ∞ F) (p : JetPolynomial.Base) {c : ℝ}
    (hN : c < ‖realNormalPart
      (primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p 0)
      (primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p 1)
      (primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p 2)‖) :
    c < ‖realSecondTensor F (baseEquiv p)‖ := by
  rw [primitiveNormalTriple_chart hF] at hN
  change c < ‖realSecondForm F SmallModes.dy SmallModes.dy (baseEquiv p)‖ at hN
  exact hN.trans_le (norm_le_pi_norm (realSecondTensor F (baseEquiv p)) (2 : Fin 3))

theorem compact_phase_normalTriple_margin
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKS : K ⊆ e.source) :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : JetPolynomial.Base → Space), ContDiff ℝ ∞ H →
      ∀ x ∈ K, ∀ c : ℝ, 0 < c →
        (let J := primitiveNormalTriple (H ∘ e.symm) (e x)
         NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖realNormalPart (J 0) (J 1) (J 2)‖) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm)
          (planeCoordinateIsometry x)) ∧
        c/D < ‖realSecondTensor (spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm)
          (planeCoordinateIsometry x)‖ := by
  let er := realPhaseChart e
  have her := realPhaseChart_smooth e he
  have hir := realPhaseChart_symm_smooth e hi
  obtain ⟨D,hD,hd⟩ := PhaseGeometry.compact_phase_chart_normal_margin er her hir
    (hK.image planeCoordinateIsometry.continuous) (by
      rintro _ ⟨x,hx,rfl⟩
      change planeCoordinateIsometry.symm (planeCoordinateIsometry x) ∈ e.source
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hKS hx)
  refine ⟨D,hD,?_⟩
  intro H hH x hx c hc hn
  let W := spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm
  let V := W ∘ er.symm
  have hW : ContDiff ℝ ∞ W := spaceCoordinates.contDiff.comp (hH.comp planeCoordinateIsometry.symm.contDiff)
  have hV : ContDiff ℝ ∞ V := hW.comp hir
  have hbase (q : JetPolynomial.Base) : baseEquiv q = planeCoordinateIsometry q := rfl
  have hrepr : (fun q => JetVelocityCoordinates.toEuclidean (V (baseEquiv q))) = H ∘ e.symm := by
    funext q
    simp only [V,W,er,hbase,realPhaseChart_symm_apply,Function.comp_apply,
      LinearIsometryEquiv.symm_apply_apply,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.symm_apply_apply]
  have htriple := hn
  rw [← hrepr] at htriple
  have hgood := good_phase_of_primitive_normal hV (e x) htriple.1
    (norm_pos_iff.mp (hc.trans htriple.2))
  have hmargin := normalTriple_secondTensor_margin hV (e x) htriple.2
  rw [hbase] at hgood hmargin
  have hrel : ∀ y ∈ er.source, W y = V (er y) := by
    intro y hy
    change W y = W (er.symm (er y))
    rw [er.left_inv hy]
  have hout := hd W V hW hV hrel (planeCoordinateIsometry x) ⟨x,hx,rfl⟩
    (by simpa only [er,realPhaseChart_apply,LinearIsometryEquiv.symm_apply_apply] using hgood.1)
    c (by simpa only [er,realPhaseChart_apply,LinearIsometryEquiv.symm_apply_apply] using hmargin)
  exact hout

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
