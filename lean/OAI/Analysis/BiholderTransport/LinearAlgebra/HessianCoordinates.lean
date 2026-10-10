import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ActualRadial
import OAI.Analysis.BiholderTransport.Coordinates.SplitLogInjective
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeSlice

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section HessianCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateNormalCost (c : TangentBundle 𝓘(ℝ,Model n) M)
    (q : (Model n×Model n)×Model n) : ℝ :=
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let a := χ.symm (q.1.1,q.2)
  let b := χ.symm q.1
  cost (riemannianExp a.1 a.2) (riemannianExp b.1 b.2)

lemma coordinateNormalCost_contDiffAt (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hp : z.2∈injectivityDomain z.1) :
    ContDiffAt ℝ ∞ (coordinateNormalCost c)
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c z,0) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let Q := (χ z,(0:Model n))
  let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
  have hzero : χ.symm ((χ z).1,0)=(⟨z.1,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    simpa only [map_zero] using tangent_chart_fiber_inverse c z hz (0:Model n)
  have hs0 : ((χ z).1,(0:Model n))∈χ.target := by
    have hf : χ (⟨z.1,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)=((χ z).1,0) := by
      apply Prod.ext
      · rfl
      · change L 0=0
        exact map_zero _
    rw [←hf]
    exact χ.map_source ((tangent_chart_source_iff c _).mpr ((tangent_chart_source_iff c z).mp hz))
  have hχ0 : ContMDiffAt 𝓘(ℝ,Model n×Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      χ.symm ((χ z).1,0) :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds hs0)
  have hχp : ContMDiffAt 𝓘(ℝ,Model n×Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      χ.symm (χ z) :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds (χ.map_source hz))
  have hA := (contMDiff_riemannianExp.contMDiffAt.comp ((χ z).1,0) hχ0).comp Q
    ((contDiffAt_fst.fst.prodMk contDiffAt_snd).contMDiffAt)
  have hB := (contMDiff_riemannianExp.contMDiffAt.comp (χ z) hχp).comp Q
    contDiffAt_fst.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain z hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2)
      (riemannianExp (χ.symm ((χ z).1,0)).1 (χ.symm ((χ z).1,0)).2,
       riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2) := by
    rw [hzero,χ.left_inv hz,riemannianExp_zero]
    exact hC
  exact (hC'.comp Q (hA.prodMk hB)).contDiffAt

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateNormalCost_slice (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
    let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
    let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
    (fun a => coordinateNormalCost c (χ z,a))=normalCost z.1 z.2 ∘ L.symm := by
  intro χ τ L
  funext a
  dsimp only [coordinateNormalCost]
  rw [tangent_chart_fiber_inverse c z hz a,χ.left_inv hz]
  rfl

lemma normalHessian_coordinate_form (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hp : z.2∈injectivityDomain z.1) (v w : TangentSpace 𝓘(ℝ,Model n) z.1) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
    let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
    normalHessian z.1 z.2 v w=
      fderiv ℝ (fderiv ℝ (coordinateNormalCost c)) (χ z,0)
        (0,τ.continuousLinearMapAt ℝ z.1 v) (0,τ.continuousLinearMapAt ℝ z.1 w) := by
  intro χ τ
  let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
  have hB := (coordinateNormalCost_contDiffAt c z hz hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := second_derivative_target_slice hB (L v) (L w)
  rw [coordinateNormalCost_slice c z hz] at H
  have hs := (normalCost_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hs' : ContDiffAt ℝ 2 (normalCost z.1 z.2) (L.symm (0:Model n)) := by
    simpa only [map_zero] using hs
  have HH := second_derivative_linear_sandwich (L.symm : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1)
    (ContinuousLinearMap.id ℝ ℝ) hs' (L v) (L w)
  simp only [id_apply,map_zero] at HH
  change fderiv ℝ (fderiv ℝ (normalCost z.1 z.2 ∘ L.symm)) 0 (L v) (L w)=
    normalHessian z.1 z.2 (L.symm (L v)) (L.symm (L w)) at HH
  rw [L.symm_apply_apply,L.symm_apply_apply] at HH
  have Hfinal := HH.symm.trans H
  simpa only [L,Trivialization.coe_continuousLinearEquivAt_eq] using Hfinal

end HessianCoordinates
end WeakMTWTransport

end

end

end

end OAI
