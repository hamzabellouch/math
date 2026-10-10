import Mathlib
import OAI.Analysis.BiholderTransport.Oscillation.SectionOscillation
import OAI.Analysis.BiholderTransport.Contact.ContactDerivative
import OAI.Analysis.BiholderTransport.Geodesics.ChartLipschitz
import OAI.Analysis.BiholderTransport.Contact.TestMountains
import OAI.Analysis.BiholderTransport.Coordinates.ActualLowerTestBound

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section SmoothTestPDE
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def chartTestContact (a b : M) (φ : Model n → ℝ) (w : Model n) : Model n :=
  coordinateContact a b (w,fderiv ℝ φ w)

lemma chartTestContact_contDiffAt {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ContDiffAt ℝ 1 (chartTestContact a b φ) z := by
  have hA : ContDiffAt ℝ 1 (coordinateContact a b) (z,fderiv ℝ φ z) :=
    (coordinateContact_contDiffAt (a := a) (b := b) (q := (z,fderiv ℝ φ z)) hz hb).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hB : ContDiffAt ℝ 1 (fun w : Model n => (w,fderiv ℝ φ w)) z :=
    contDiffAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num))
  exact hA.comp (f := fun w : Model n => (w,fderiv ℝ φ w)) z hB

variable [Nonempty M] [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_strict_test_det_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a))) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let b := coordinateBackward a (-1,z,L)
    ∃ K≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z → fderiv ℝ φ z=L →
      uv.1 a=φ z →
      (∃ ε>0, ∀ᶠ w : Model n in 𝓝 z,
        ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∃ m>0, ∀ d : Model n, m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d) →
      |(fderiv ℝ (chartTestContact a b φ) z).det|≤K := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let z := χ a
  let b := coordinateBackward a (-1,z,L)
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  have hz : z∈χ.target := χ.map_source (mem_extChartAt_source a)
  have hza : χ.symm z=a := χ.left_inv (mem_extChartAt_source a)
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨Da,r₁,hr₁,hchart₁,hDa⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  obtain ⟨Cb,R,hR,hT,hCb⟩ := exists_lipschitzOn_chart (n := n) b
  let K := (cap/lam)*((Cb:ℝ)*(Da:ℝ))^n
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro x0 uv huv φ hφ hL hval hgap hpos
  obtain ⟨ε,hε,hgap⟩ := hgap
  obtain ⟨m,hm,hpos⟩ := hpos
  have hpφ : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain (χ.symm z) := by rwa [hL]
  have hpos' : ∀ d : Model n, m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d := by
    change fderiv ℝ φ z=L at hL
    rw [hL]
    exact hpos
  obtain ⟨r₂,hr₂,_,hmount⟩ := exists_test_mountains hz hφ hpφ hm hpos'
  let Y := fun w : Model n => coordinateBackward a (-1,w,fderiv ℝ φ w)
  have hYz : Y z=b := by dsimp [Y,b]; rw [hL]
  have hY : ContinuousAt Y z :=
    (coordinateBackward_contMDiffAt (q := (-1,z,fderiv ℝ φ z)) hz).continuousAt.comp
      (x := z) (f := fun w : Model n => ((-1:ℝ),w,fderiv ℝ φ w))
      (continuousAt_const.prodMk (continuousAt_id.prodMk
        (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt))
  have hYn : ∀ᶠ w : Model n in 𝓝 z, Y w∈Metric.ball b R :=
    hY.preimage_mem_nhds (by rw [hYz]; exact Metric.ball_mem_nhds b hR)
  have hnear : ∀ᶠ w : Model n in 𝓝 z,
      ε*dist w z^2≤uv.1 (χ.symm w)-φ w ∧
      w∈Metric.ball z r₁ ∧ w∈Metric.ball z r₂ ∧
      ContinuousAt φ w ∧ Y w∈Metric.ball b R :=
    by
      filter_upwards [hgap,Metric.ball_mem_nhds z hr₁,Metric.ball_mem_nhds z hr₂,
        hφ.eventually (by norm_num),hYn] with w hw h₁ h₂ hφw hYw
      exact ⟨hw,h₁,h₂,hφw.continuousAt,hYw⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  obtain ⟨rho0,rho1,hrho0,hrho1,hmin⟩ := huv.2
  apply hmtw.lower_test_chart_det_bound hlam hcap hrho0 hrho1
    (densityDualClass_isDual huv) hmin hr hε
    (fun w hw => hchart₁ (hrsub hw).2.1)
    (hDa.mono (fun w hw => (hrsub hw).2.1)) hCb
    (fun w hw => (hrsub hw).2.2.2.1.continuousWithinAt)
    (by change uv.1 (χ.symm z)=φ z; rw [hza]; exact hval) (fun w hw => (hrsub hw).1)
    (S := chartTestContact a b φ) ?_ ?_
    ((chartTestContact_contDiffAt hz hφ (by change Y z∈ψ.source; rw [hYz]; exact mem_extChartAt_source b)).hasStrictFDerivAt (by norm_num))
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

end SmoothTestPDE
end WeakMTWTransport

end

end

end

end OAI
