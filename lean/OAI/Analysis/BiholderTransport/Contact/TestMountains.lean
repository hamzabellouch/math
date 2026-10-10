import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.LocalMountains
import OAI.Analysis.BiholderTransport.Coordinates.ChartGradientMap
import OAI.Analysis.BiholderTransport.Regularity.SecondFderivAdd

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TestMountains
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma exists_test_mountains {a : M} {z : Model n} {φ : Model n → ℝ} {m : ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z)) (hm : 0 < m)
    (hpos : ∀ d : Model n, m*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ φ) z d d +
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) :
    ∃ r>0, Metric.closedBall z r⊆(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ w∈Metric.closedBall z r, ∀ q∈Metric.closedBall z r,
        φ w+chartCost a (coordinateBackward a (-1,w,fderiv ℝ φ w)) w ≤
          φ q+chartCost a (coordinateBackward a (-1,w,fderiv ℝ φ w)) q := by
  let Y := fun w => coordinateBackward a (-1,w,fderiv ℝ φ w)
  let F := fun y w => φ w+chartCost a y w
  have hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,Y z) := by
    rw [show Y z=riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm z)
      (chartGradientVector a z (fderiv ℝ φ z)) from coordinateBackward_eq_exp_chartGradient hz _]
    exact cost_contMDiffAt_of_injectivityDomain
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z (fderiv ℝ φ z)⟩ :
        TangentBundle 𝓘(ℝ,Model n) M) hp
  obtain ⟨hC,hD⟩ := chartCost_jet_continuous hz hc
  have hDn : ∀ᶠ q : Model n×M in 𝓝 (z,Y z), ContDiffAt ℝ 2 φ q.1 :=
    continuousAt_fst.eventually (hφ.eventually (by norm_num))
  have he : ∀ᶠ q : Model n×M in 𝓝 (z,Y z),
      fderiv ℝ (fderiv ℝ (F q.2)) q.1 =
        fderiv ℝ (fderiv ℝ φ) q.1+fderiv ℝ (fderiv ℝ (chartCost a q.2)) q.1 := by
    filter_upwards [hDn,hD] with q hq hq'
    exact second_fderiv_add_eq hq hq'
  have hFC : ContinuousAt (fun q : Model n×M => fderiv ℝ (fderiv ℝ (F q.2)) q.1) (z,Y z) := by
    apply ((((hφ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.comp continuousAt_fst).add hC).congr_of_eventuallyEq he
  have hFD : ∀ᶠ q : Model n×M in 𝓝 (z,Y z), ContDiffAt ℝ 2 (F q.2) q.1 := by
    filter_upwards [hDn,hD] with q hq hq'
    exact hq.add hq'
  obtain ⟨r₀,hr₀,V,hV,H⟩ := exists_local_mountains hm hFC hFD (by
    intro d
    rw [he.self_of_nhds]
    exact hpos d)
  have hj : ContinuousAt (fun w : Model n => (w,fderiv ℝ φ w)) z :=
    continuousAt_id.prodMk ((hφ.fderiv_right (m := 1) (by norm_num)).continuousAt)
  have hY : ContinuousAt Y z :=
    (coordinateBackward_contMDiffAt (q := (-1,z,fderiv ℝ φ z)) hz).continuousAt.comp (x := z) (f := fun w : Model n => ((-1:ℝ),w,fderiv ℝ φ w))
      (continuousAt_const.prodMk hj)
  have hchart : ∀ᶠ w : Model n in 𝓝 z, w∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (isOpen_extChartAt_target a).mem_nhds hz
  have hnear : ∀ᶠ w : Model n in 𝓝 z,
      w∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
      chartGradientVector a w (fderiv ℝ φ w)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm w) ∧
      ContDiffAt ℝ 2 φ w ∧ Y w∈V ∧ w∈Metric.ball z r₀ :=
    by
      filter_upwards [hchart,hj.eventually (chartGradientVector_regular_near hz hp),
        hφ.eventually (by norm_num),hY.preimage_mem_nhds hV,Metric.ball_mem_nhds z hr₀]
        with w hw hpw hφw hyw hrw
      exact ⟨hw,hpw,hφw,hyw,hrw⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  refine ⟨r,hr,fun w hw => (hrsub hw).1,?_⟩
  intro w hw q hq
  have hw' := hrsub hw
  apply H (Y w) hw'.2.2.2.1 w (Metric.ball_subset_closedBall hw'.2.2.2.2) ?_
    q (Metric.ball_subset_closedBall (hrsub hq).2.2.2.2)
  have HD := (hw'.2.2.1.differentiableAt (by norm_num)).hasFDerivAt.add
    (chartCost_gradient_at_contact hw'.1 hw'.2.1)
  change fderiv ℝ (φ + chartCost a (coordinateBackward a (-1,w,fderiv ℝ φ w))) w=0
  simpa only [add_neg_cancel] using HD.fderiv

end TestMountains
end WeakMTWTransport

end

end

end

end OAI
