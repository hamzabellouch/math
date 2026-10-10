import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ContactStationarity

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactStationarity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartTestContact_relative_hessian_fixed {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
    let y := extChartAt 𝓘(ℝ,Model n) b c
    let D := fderiv ℝ (chartCostCovector a b) (z,y)
    fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z =
      -((D.comp (ContinuousLinearMap.inr ℝ (Model n) (Model n))).comp
        (fderiv ℝ (chartTestContact a b φ) z)) := by
  dsimp only
  let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let y := extChartAt 𝓘(ℝ,Model n) b c
  let G := chartCostCovector (n := n) a b
  let T := chartTestContact a b φ
  have hTy : T z=y := rfl
  have hy : y∈(extChartAt 𝓘(ℝ,Model n) b).target :=
    (extChartAt 𝓘(ℝ,Model n) b).map_source hb
  have hyb : (extChartAt 𝓘(ℝ,Model n) b).symm y=c :=
    (extChartAt 𝓘(ℝ,Model n) b).left_inv hb
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z (fderiv ℝ φ z)⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,
        (extChartAt 𝓘(ℝ,Model n) b).symm y) := by
    rw [hyb,show c=riemannianExp _ (chartGradientVector a z (fderiv ℝ φ z)) from
      coordinateBackward_eq_exp_chartGradient hz _]
    exact hc
  have hG : DifferentiableAt ℝ G (z,y) :=
    (chartCostCovector_contDiffAt hz hy hc').differentiableAt (by simp)
  have hT : DifferentiableAt ℝ T z :=
    (chartTestContact_contDiffAt hz hφ hb).differentiableAt (by simp)
  have hgraph : HasFDerivAt (fun w => (w,T w))
      ((ContinuousLinearMap.id ℝ (Model n)).prod (fderiv ℝ T z)) z :=
    (hasFDerivAt_id z).prodMk hT.hasFDerivAt
  have hggraph := hG.hasFDerivAt.comp z hgraph
  have he : (fun w => G (w,T w))=ᶠ[𝓝 z] (fun w => -fderiv ℝ φ w) := by
    have hZ : ContinuousAt (fun w => (w,fderiv ℝ φ w)) z :=
      continuousAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact hZ.eventually (contact_stationarity_eventually hz hp hb)
  have heD := (hggraph.congr_of_eventuallyEq he.symm).unique
    (((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.neg)
  have hbaseMap : HasFDerivAt (fun w : Model n => (w,y))
      ((ContinuousLinearMap.id ℝ (Model n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hbase := hG.hasFDerivAt.comp (f := fun w : Model n => (w,y)) z hbaseMap
  have hbaseEq : (fun w => G (w,y))=fderiv ℝ (chartCost a c) := by
    funext w
    change fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm y)) w = _
    rw [hyb]
  change HasFDerivAt (fun w => G (w,y)) _ z at hbase
  rw [hbaseEq] at hbase
  have hbaseD := hbase.fderiv
  ext ξ η
  have heV := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A ξ η) heD
  have hbV := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A ξ η) hbaseD
  dsimp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply,
    neg_apply,Pi.neg_apply] at heV hbV
  have hsplit : (ξ,fderiv ℝ T z ξ)=(ξ,(0:Model n))+(0,fderiv ℝ T z ξ) := by simp
  rw [hsplit,map_add,add_apply] at heV
  change fderiv ℝ (fderiv ℝ φ) z ξ η+fderiv ℝ (fderiv ℝ (chartCost a c)) z ξ η =
    -fderiv ℝ G (z,y) (0,fderiv ℝ T z ξ) η
  simp only [neg_apply,zero_apply] at heV hbV
  linarith only [heV,hbV]

end ContactStationarity
end WeakMTWTransport

end

end

end

end OAI
