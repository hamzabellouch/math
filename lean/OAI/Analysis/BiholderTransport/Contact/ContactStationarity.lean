import Mathlib
import OAI.Analysis.BiholderTransport.Contact.SmoothTestPDE

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactStationarity
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

def chartCostCovector (a b : M) (q : Model n×Model n) : Model n →L[ℝ] ℝ :=
  fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm q.2)) q.1

lemma chartCostCovector_contDiffAt {a b : M} {q : Model n×Model n}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : q.2∈(extChartAt 𝓘(ℝ,Model n) b).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1,(extChartAt 𝓘(ℝ,Model n) b).symm q.2)) :
    ContDiffAt ℝ ∞ (chartCostCovector a b) q := by
  let F : Model n → Model n → ℝ := fun y x =>
    chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm y) x
  have hiA := (contMDiffOn_extChartAt_symm (n := ∞) a).contMDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ha)
  have hiB := (contMDiffOn_extChartAt_symm (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hb)
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) q.swap :=
    (hc.comp q.swap ((hiA.comp q.swap contDiffAt_snd.contMDiffAt).prodMk
      (hiB.comp q.swap contDiffAt_fst.contMDiffAt))).contDiffAt
  exact (ContDiffAt.partial_snd_fderiv hF).comp q (contDiffAt_snd.prodMk contDiffAt_fst)

variable [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contact_stationarity_eventually {a b : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a q.1 q.2∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1))
    (hb : coordinateBackward a (-1,q.1,q.2)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ∀ᶠ q' in 𝓝 q, chartCostCovector a b (q'.1,coordinateContact a b q')= -q'.2 := by
  have hY : ContinuousAt (fun q : Model n×(Model n →L[ℝ] ℝ) => coordinateBackward a (-1,q.1,q.2)) q :=
    (coordinateBackward_contMDiffAt (q := (-1,q.1,q.2)) ha).continuousAt.comp
      (x := q) (continuousAt_const.prodMk continuousAt_id)
  have hT := hY.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb)
  have hA := continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds ha)
  filter_upwards [hT,hA,chartGradientVector_regular_near ha hp] with q' hb' ha' hp'
  dsimp only [chartCostCovector,coordinateContact]
  rw [(extChartAt 𝓘(ℝ,Model n) b).left_inv hb']
  exact (chartCost_gradient_at_contact ha' hp').fderiv

lemma chartTestContact_relative_hessian {a : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z)) :
    let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
    let y := extChartAt 𝓘(ℝ,Model n) b b
    let D := fderiv ℝ (chartCostCovector a b) (z,y)
    fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a b)) z =
      -((D.comp (ContinuousLinearMap.inr ℝ (Model n) (Model n))).comp
        (fderiv ℝ (chartTestContact a b φ) z)) := by
  dsimp only
  let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let y := extChartAt 𝓘(ℝ,Model n) b b
  let G := chartCostCovector (n := n) a b
  let T := chartTestContact a b φ
  have hTy : T z=y := rfl
  have hy : y∈(extChartAt 𝓘(ℝ,Model n) b).target :=
    (extChartAt 𝓘(ℝ,Model n) b).map_source (mem_extChartAt_source b)
  have hyb : (extChartAt 𝓘(ℝ,Model n) b).symm y=b :=
    (extChartAt 𝓘(ℝ,Model n) b).left_inv (mem_extChartAt_source b)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z (fderiv ℝ φ z)⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,
        (extChartAt 𝓘(ℝ,Model n) b).symm y) := by
    rw [hyb,show b=riemannianExp _ (chartGradientVector a z (fderiv ℝ φ z)) from
      coordinateBackward_eq_exp_chartGradient hz _]
    exact hc
  have hG : DifferentiableAt ℝ G (z,y) :=
    (chartCostCovector_contDiffAt hz hy hc').differentiableAt (by simp)
  have hT : DifferentiableAt ℝ T z :=
    (chartTestContact_contDiffAt hz hφ (mem_extChartAt_source b)).differentiableAt (by simp)
  have hgraph : HasFDerivAt (fun w => (w,T w))
      ((ContinuousLinearMap.id ℝ (Model n)).prod (fderiv ℝ T z)) z :=
    (hasFDerivAt_id z).prodMk hT.hasFDerivAt
  have hggraph := hG.hasFDerivAt.comp z hgraph
  have he : (fun w => G (w,T w))=ᶠ[𝓝 z] (fun w => -fderiv ℝ φ w) := by
    have hZ : ContinuousAt (fun w => (w,fderiv ℝ φ w)) z :=
      continuousAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact hZ.eventually (contact_stationarity_eventually hz hp (mem_extChartAt_source b))
  have heD := (hggraph.congr_of_eventuallyEq he.symm).unique
    (((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.neg)
  have hbaseMap : HasFDerivAt (fun w : Model n => (w,y))
      ((ContinuousLinearMap.id ℝ (Model n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hbase := hG.hasFDerivAt.comp (f := fun w : Model n => (w,y)) z hbaseMap
  have hbaseEq : (fun w => G (w,y))=fderiv ℝ (chartCost a b) := by
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
  change fderiv ℝ (fderiv ℝ φ) z ξ η+fderiv ℝ (fderiv ℝ (chartCost a b)) z ξ η =
    -fderiv ℝ G (z,y) (0,fderiv ℝ T z ξ) η
  simp only [neg_apply,zero_apply] at heV hbV
  linarith only [heV,hbV]

end ContactStationarity
end WeakMTWTransport

end

end

end

end OAI
