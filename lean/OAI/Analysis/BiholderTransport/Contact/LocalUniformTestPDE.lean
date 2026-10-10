import Mathlib
import OAI.Analysis.BiholderTransport.Contact.SmoothTestPDE

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section LocalUniformTestPDE
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

variable [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_locally_uniform_test_det_bound
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (a b : M) :
    ∃ U : Set (Model n), IsOpen U ∧ extChartAt 𝓘(ℝ,Model n) a a∈U ∧
    ∃ V : Set M, IsOpen V ∧ b∈V ∧
    ∃ K≥0, ∀ z∈U, ∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z →
      coordinateBackward a (-1,z,fderiv ℝ φ z)∈V →
      chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) →
      uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z →
      (∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∃ m>0,∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) →
      |(fderiv ℝ (chartTestContact a b φ) z).det|≤K := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨Da,r₁,hr₁,hchart₁,hDa⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  obtain ⟨Cb,R,hR,hT,hCb⟩ := exists_lipschitzOn_chart (n := n) b
  let U := Metric.ball (χ a) r₁
  let V := Metric.ball b R
  let K := (cap/lam)*((Cb:ℝ)*(Da:ℝ))^n
  refine ⟨U,Metric.isOpen_ball,Metric.mem_ball_self hr₁,V,Metric.isOpen_ball,
    Metric.mem_ball_self hR,K,by dsimp [K]; positivity,?_⟩
  intro z hz x0 uv huv φ hφ hYz hpφ hval hgap hpos
  have hzT : z∈χ.target := hchart₁ hz
  obtain ⟨ε,hε,hgap⟩ := hgap
  obtain ⟨m,hm,hpos⟩ := hpos
  obtain ⟨r₂,hr₂,_,hmount⟩ := exists_test_mountains hzT hφ hpφ hm hpos
  let Y := fun w : Model n => coordinateBackward a (-1,w,fderiv ℝ φ w)
  have hY : ContinuousAt Y z :=
    (coordinateBackward_contMDiffAt (q := (-1,z,fderiv ℝ φ z)) hzT).continuousAt.comp
      (x := z) (f := fun w : Model n => ((-1:ℝ),w,fderiv ℝ φ w))
      (continuousAt_const.prodMk (continuousAt_id.prodMk
        (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt))
  have hYn : ∀ᶠ w : Model n in 𝓝 z,Y w∈V :=
    hY.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hYz)
  have hnear : ∀ᶠ w : Model n in 𝓝 z,
      ε*dist w z^2≤uv.1 (χ.symm w)-φ w ∧
      w∈U ∧ w∈Metric.ball z r₂ ∧ ContinuousAt φ w ∧ Y w∈V := by
    filter_upwards [hgap,Metric.isOpen_ball.mem_nhds hz,Metric.ball_mem_nhds z hr₂,
      hφ.eventually (by norm_num),hYn] with w hw h₁ h₂ hφw hYw
    exact ⟨hw,h₁,h₂,hφw.continuousAt,hYw⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  obtain ⟨rho0,rho1,hrho0,hrho1,hmin⟩ := huv.2
  apply hmtw.lower_test_chart_det_bound hlam hcap hrho0 hrho1
    (densityDualClass_isDual huv) hmin hr hε
    (fun w hw => hchart₁ (hrsub hw).2.1)
    (hDa.mono (fun w hw => (hrsub hw).2.1)) hCb
    (fun w hw => (hrsub hw).2.2.2.1.continuousWithinAt)
    hval (fun w hw => (hrsub hw).1) (S := chartTestContact a b φ) ?_ ?_
    ((chartTestContact_contDiffAt hzT hφ (hT hYz)).hasStrictFDerivAt (by norm_num))
  · intro w hw
    have hy : Y w∈ψ.source := hT (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
    refine ⟨ψ.map_source hy,?_⟩
    change ψ.symm (ψ (Y w))∈Metric.ball b R
    rw [ψ.left_inv hy]
    exact (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
  · intro w hw q hq
    have hy : Y w∈ψ.source := hT (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
    change φ w+cost (χ.symm w) (ψ.symm (ψ (Y w)))≤φ q+cost (χ.symm q) (ψ.symm (ψ (Y w)))
    rw [ψ.left_inv hy]
    exact hmount w (Metric.ball_subset_closedBall (hrsub (Metric.ball_subset_closedBall hw)).2.2.1)
      q (Metric.ball_subset_closedBall (hrsub hq).2.2.1)

end LocalUniformTestPDE
end WeakMTWTransport

end

end

end

end OAI
