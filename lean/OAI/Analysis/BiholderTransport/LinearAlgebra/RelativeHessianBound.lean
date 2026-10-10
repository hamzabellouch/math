import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ContactStationarity
import OAI.Analysis.BiholderTransport.Contact.LocalUniformTestPDE
import OAI.Analysis.BiholderTransport.LinearAlgebra.NormDetCoercivity

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section RelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def mixedCostOperator (a b : M) (z y : Model n) : Model n →L[ℝ] Model n :=
  bilinearOperator (-((fderiv ℝ (chartCostCovector a b) (z,y)).comp
    (ContinuousLinearMap.inr ℝ (Model n) (Model n))))

omit [Nonempty M] in
lemma relative_hessian_operator_factor {a : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z)) :
    let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
    bilinearOperator (fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a b)) z) =
      (mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b b)).comp
        (fderiv ℝ (chartTestContact a b φ) z) := by
  dsimp only
  rw [chartTestContact_relative_hessian hz hφ hp]
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  simp only [ContinuousLinearMap.comp_apply,bilinearOperator_inner,mixedCostOperator,
    neg_apply]

variable [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_strict_relative_hessian_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (hcap : 0≤cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m : ℝ} (hm : 0 < m) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let b := coordinateBackward a (-1,z,L)
    ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z → fderiv ℝ φ z=L → uv.1 a=φ z →
      (∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d≤C*‖d‖^2 := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let b := coordinateBackward a (-1,z,L)
  let B := mixedCostOperator (n := n) a b z (extChartAt 𝓘(ℝ,Model n) b b)
  obtain ⟨K,hK0,hK⟩ := hmtw.exists_strict_test_det_bound hlam hcap a L hp
  let C := (finrank ℝ (Model n):ℝ)*(|B.det| *K)/m^(finrank ℝ (Model n)-1)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro x0 uv huv φ hφ hL hval hgap hpos d
  have hdet := hK x0 uv huv φ hφ hL hval hgap ⟨m,hm,hpos⟩
  let W := fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a b)) z
  have hfactor : bilinearOperator W=B.comp (fderiv ℝ (chartTestContact a b φ) z) := by
    have H := relative_hessian_operator_factor
      ((extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)) hφ
      (show chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) from by rwa [hL])
    simpa only [hL] using H
  have hWdet : |(bilinearOperator W).det|≤|B.det| *K := by
    rw [hfactor]
    change |(B.toLinearMap.comp (fderiv ℝ (chartTestContact a b φ) z).toLinearMap).det|≤_
    rw [LinearMap.det_comp,abs_mul]
    exact mul_le_mul_of_nonneg_left hdet (abs_nonneg _)
  exact bilinear_quadratic_bound_of_det hm hpos hWdet d

end RelativeHessianBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalUniformRelativeHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma relative_hessian_operator_factor_fixed {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
    bilinearOperator (fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z) =
      (mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b c)).comp
        (fderiv ℝ (chartTestContact a b φ) z) := by
  dsimp only
  rw [chartTestContact_relative_hessian_fixed hz hφ hp hb]
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  simp only [ContinuousLinearMap.comp_apply,bilinearOperator_inner,mixedCostOperator,
    neg_apply]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mixedCostOperator_continuousAt {a b : M} {q : Model n×Model n}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : q.2∈(extChartAt 𝓘(ℝ,Model n) b).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1,(extChartAt 𝓘(ℝ,Model n) b).symm q.2)) :
    ContinuousAt (fun q : Model n×Model n => mixedCostOperator a b q.1 q.2) q := by
  have H := ((chartCostCovector_contDiffAt ha hb hc).fderiv_right
    (m := 0) (by simp)).continuousAt
  exact continuousAt_const.clm_comp ((H.clm_comp continuousAt_const).neg)

variable [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_strict_relative_hessian_bound
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0<lam) (hcap : 0≤cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m : ℝ} (hm : 0 < m) :
    let za := extChartAt 𝓘(ℝ,Model n) a a
    ∃ N : Set (Model n×(Model n →L[ℝ] ℝ)), N∈𝓝 (za,L) ∧
    ∃ C≥0,∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ (z : Model n) (φ : Model n → ℝ), (z,fderiv ℝ φ z)∈N →
      ContDiffAt ℝ 2 φ z →
      uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z →
      (∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d≤C*‖d‖^2 := by
  dsimp only
  let za := extChartAt 𝓘(ℝ,Model n) a a
  let b := coordinateBackward a (-1,za,L)
  let yb := extChartAt 𝓘(ℝ,Model n) b b
  let Y := fun q : Model n×(Model n →L[ℝ] ℝ) => coordinateBackward a (-1,q.1,q.2)
  let J := fun q : Model n×(Model n →L[ℝ] ℝ) => (q.1,extChartAt 𝓘(ℝ,Model n) b (Y q))
  have ha : za∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hb : yb∈(extChartAt 𝓘(ℝ,Model n) b).target :=
    (extChartAt 𝓘(ℝ,Model n) b).map_source (mem_extChartAt_source b)
  have hY : ContinuousAt Y (za,L) :=
    (coordinateBackward_contMDiffAt (q := (-1,za,L)) ha).continuousAt.comp
      (x := (za,L)) (continuousAt_const.prodMk continuousAt_id)
  have hJ : ContinuousAt J (za,L) := continuousAt_fst.prodMk
    ((show ContinuousAt (extChartAt 𝓘(ℝ,Model n) b) (Y (za,L)) from continuousAt_extChartAt b).comp (x := (za,L)) (f := Y) hY)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm za,chartGradientVector a za L⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z:M×M => cost z.1 z.2)
      ((extChartAt 𝓘(ℝ,Model n) a).symm za,(extChartAt 𝓘(ℝ,Model n) b).symm yb) := by
    rw [(extChartAt 𝓘(ℝ,Model n) b).left_inv (mem_extChartAt_source b)]
    rw [show b=riemannianExp _ (chartGradientVector a za L) from coordinateBackward_eq_exp_chartGradient ha _]
    exact hc
  let F := fun q : Model n×(Model n →L[ℝ] ℝ) =>
    |(mixedCostOperator a b (J q).1 (J q).2).det|
  have hF : ContinuousAt F (za,L) :=
    (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((mixedCostOperator_continuousAt ha hb hc').comp hJ)).abs
  let B := F (za,L)+1
  have hB : 0≤B := by dsimp [B,F]; positivity
  have hFn : ∀ᶠ q in 𝓝 (za,L),F q≤B :=
    (hF.eventually (gt_mem_nhds (show F (za,L)<B by dsimp [B]; linarith))).mono (fun _ h => h.le)
  obtain ⟨U,hU,haU,V,hV,hbV,K,hK,HK⟩ := hmtw.exists_locally_uniform_test_det_bound hlam hcap a b
  let N := {q : Model n×(Model n →L[ℝ] ℝ) | q.1∈U ∧
    q.1∈(extChartAt 𝓘(ℝ,Model n) a).target ∧ Y q∈V ∧
    Y q∈(extChartAt 𝓘(ℝ,Model n) b).source ∧
    chartGradientVector a q.1 q.2∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) ∧ F q≤B}
  have hN : N∈𝓝 (za,L) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hU.mem_nhds haU),
      continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds ha),
      hY.preimage_mem_nhds (hV.mem_nhds hbV),
      hY.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) b),
      chartGradientVector_regular_near ha hp,hFn] with q h₁ h₂ h₃ h₄ h₅ h₆
    exact ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  let C := (finrank ℝ (Model n):ℝ)*(B*K)/m^(finrank ℝ (Model n)-1)
  refine ⟨N,hN,C,by dsimp [C]; positivity,?_⟩
  intro x0 uv huv z φ hz hφ hval hgap hpos d
  obtain ⟨hzU,hzT,hYV,hYS,hpφ,hBφ⟩ := hz
  have hdet := HK z hzU x0 uv huv φ hφ hYV hpφ hval hgap ⟨m,hm,hpos⟩
  let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let W := fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z
  have hfactor := relative_hessian_operator_factor_fixed hzT hφ hpφ hYS
  have hWdet : |(bilinearOperator W).det|≤B*K := by
    rw [hfactor]
    change |((mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b c)).toLinearMap.comp
      (fderiv ℝ (chartTestContact a b φ) z).toLinearMap).det|≤_
    rw [LinearMap.det_comp,abs_mul]
    exact mul_le_mul hBφ hdet (abs_nonneg _) hB
  exact bilinear_quadratic_bound_of_det hm hpos hWdet d

end LocalUniformRelativeHessian
end WeakMTWTransport

end

end

end

end OAI
