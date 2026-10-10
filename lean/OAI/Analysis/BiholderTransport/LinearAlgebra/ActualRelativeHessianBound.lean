import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.RelativeHessianBound
import OAI.Analysis.BiholderTransport.Regularity.CenteredQuadratic

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ActualRelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_relative_hessian_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (hcap : 0≤cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m : ℝ} (hm : 0 < m) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let b := coordinateBackward a (-1,z,L)
    ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z → fderiv ℝ φ z=L → uv.1 a=φ z →
      (∀ᶠ w in 𝓝 z,φ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d≤C*‖d‖^2 := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let b := coordinateBackward a (-1,z,L)
  obtain ⟨C,hC,H⟩ := hmtw.exists_strict_relative_hessian_bound hlam hcap a L hp
    (show 0 < m/2 by positivity)
  refine ⟨C+m/2,by positivity,?_⟩
  intro x0 uv huv φ hφ hL hval hlo hpos d
  change fderiv ℝ φ z=L at hL
  change uv.1 a=φ z at hval
  let q : Model n → ℝ := fun w => ‖w-z‖^2/2
  let ψ : Model n → ℝ := fun w => φ w-(m/2)*q w
  have hq : ContDiffAt ℝ 2 q z := (centered_half_norm_sq_c2 z).contDiffAt
  have hψ : ContDiffAt ℝ 2 ψ z := hφ.sub (contDiffAt_const.mul hq)
  have hψL : fderiv ℝ ψ z=L := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      fderiv_fun_sub (hφ.differentiableAt (by norm_num))
        ((hq.differentiableAt (by norm_num)).const_mul _)]
    change fderiv ℝ φ z-fderiv ℝ ((m/2) • q) z=L
    rw [fderiv_const_smul_field,Pi.smul_apply,centered_half_norm_sq_fderiv,smul_zero,sub_zero,hL]
  have hψval : uv.1 a=ψ z := by simpa [ψ,q] using hval
  have hgap : ∃ ε>0,∀ᶠ w in 𝓝 z,
      ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-ψ w := by
    refine ⟨m/4,by positivity,?_⟩
    filter_upwards [hlo] with w hw
    dsimp only [ψ,q]
    rw [dist_eq_norm]
    nlinarith only [hw]
  have hψH (e : Model n) : fderiv ℝ (fderiv ℝ ψ) z e e=
      fderiv ℝ (fderiv ℝ φ) z e e-(m/2)*‖e‖^2 := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      second_fderiv_sub hφ (contDiffAt_const.mul hq),second_fderiv_const_mul,
      centered_half_norm_sq_second]
  have hpψ : ∀ e : Model n,(m/2)*‖e‖^2≤fderiv ℝ (fderiv ℝ ψ) z e e+
      fderiv ℝ (fderiv ℝ (chartCost a b)) z e e := by
    intro e
    rw [hψH]
    linarith only [hpos e]
  have HD := H x0 uv huv ψ hψ hψL hψval hgap hpψ d
  rw [hψH] at HD
  nlinarith only [HD]

end ActualRelativeHessianBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ActualRelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_relative_hessian_bound
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
      (∀ᶠ w in 𝓝 z,φ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d≤C*‖d‖^2 := by
  dsimp only
  obtain ⟨N,hN,C,hC,H⟩ := hmtw.exists_local_strict_relative_hessian_bound hlam hcap a L hp
    (show 0 < m/2 by positivity)
  refine ⟨N,hN,C+m/2,by positivity,?_⟩
  intro x0 uv huv z φ hz hφ hval hlo hpos d
  let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let q : Model n → ℝ := fun w => ‖w-z‖^2/2
  let ψ : Model n → ℝ := fun w => φ w-(m/2)*q w
  have hq : ContDiffAt ℝ 2 q z := (centered_half_norm_sq_c2 z).contDiffAt
  have hψ : ContDiffAt ℝ 2 ψ z := hφ.sub (contDiffAt_const.mul hq)
  have hψL : fderiv ℝ ψ z=fderiv ℝ φ z := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      fderiv_fun_sub (hφ.differentiableAt (by norm_num))
        ((hq.differentiableAt (by norm_num)).const_mul _)]
    change fderiv ℝ φ z-fderiv ℝ ((m/2) • q) z=fderiv ℝ φ z
    rw [fderiv_const_smul_field,Pi.smul_apply,centered_half_norm_sq_fderiv,smul_zero,sub_zero]
  have hψval : uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=ψ z := by simpa [ψ,q] using hval
  have hgap : ∃ ε>0,∀ᶠ w in 𝓝 z,
      ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-ψ w := by
    refine ⟨m/4,by positivity,?_⟩
    filter_upwards [hlo] with w hw
    dsimp only [ψ,q]
    rw [dist_eq_norm]
    nlinarith only [hw]
  have hψH (e : Model n) : fderiv ℝ (fderiv ℝ ψ) z e e=
      fderiv ℝ (fderiv ℝ φ) z e e-(m/2)*‖e‖^2 := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      second_fderiv_sub hφ (contDiffAt_const.mul hq),second_fderiv_const_mul,
      centered_half_norm_sq_second]
  have hpψ : ∀ e : Model n,(m/2)*‖e‖^2≤fderiv ℝ (fderiv ℝ ψ) z e e+
      fderiv ℝ (fderiv ℝ (chartCost a b)) z e e := by
    intro e
    rw [hψH]
    linarith only [hpos e]
  have HD := H x0 uv huv z ψ (by rw [hψL]; exact hz) hψ hψval hgap
    (by simpa only [hψL] using hpψ) d
  rw [hψH,hψL] at HD
  nlinarith only [HD]

end ActualRelativeHessianBound
end WeakMTWTransport

end

end

end

end OAI
