import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.NormLower
import OAI.Analysis.BiholderTransport.LinearAlgebra.ActualRelativeHessianBound
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateTrueLog

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section NormalRelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_normal_relative_hessian_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) {a : M}
    {p : TangentSpace 𝓘(ℝ,Model n) a} (hp : p∈injectivityDomain a)
    {m : ℝ} (hm : 0 < m) :
    ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : TangentSpace 𝓘(ℝ,Model n) a → ℝ,
      ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p → uv.1 a=φ 0 →
      (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp a w)) →
      (∀ d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d) →
      ∀ d,fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d≤C*‖d‖^2 := by
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let V := TangentSpace 𝓘(ℝ,Model n) a
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) a) := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let c := normalCost a p
  obtain ⟨L,hLreg,hLb,hLD⟩ := exists_chart_covector_for_log hp
  obtain ⟨e,he,he0,hei,hi⟩ := exists_smooth_chart_fiber_log (a := a)
    (zero_mem_injectivityDomain (n := n) a)
    (by simpa only [riemannianExp_zero] using mem_extChartAt_source (I := 𝓘(ℝ,Model n)) a)
  simp only [riemannianExp_zero] at he he0 hei hi
  change ContDiffAt ℝ ∞ e z at he
  change e z=0 at he0
  change Function.Injective (fderiv ℝ e z) at hi
  have he2 : ContDiffAt ℝ 2 e z := he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨k,hk,Hk⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ e z) hi
  have hsur : Function.Surjective (fderiv ℝ e z) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hi
  obtain ⟨C,hC,HC⟩ := hmtw.exists_relative_hessian_bound hlam hcap a L hLreg (mul_pos hm hk)
  refine ⟨C/k,div_nonneg hC hk.le,?_⟩
  intro x0 uv huv φ hφ hφD hval hlo hpos d
  let ψ : Model n → ℝ := fun w => φ (e w)
  have hψ : ContDiffAt ℝ 2 ψ z := (he0.symm ▸ hφ).comp z he2
  have hc : ContDiffAt ℝ 2 c 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hce : chartCost a (riemannianExp a p) =ᶠ[𝓝 z] (fun w => c (e w)) := by
    filter_upwards [hei] with w hw
    simp only [c,normalCost,chartCost,hw]
  have hcc : ContDiffAt ℝ 2 (chartCost a (riemannianExp a p)) z :=
    ((he0.symm ▸ hc).comp z he2).congr_of_eventuallyEq hce
  have hψD : fderiv ℝ ψ z=L := by
    have Hc := hce.fderiv_eq (𝕜 := ℝ)
    rw [hLD.fderiv,fderiv_fun_comp z
      (by simpa only [he0] using hc.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,(normalCost_hasFDerivAt_zero hp).fderiv] at Hc
    rw [show ψ=(fun w => φ (e w)) from rfl,fderiv_fun_comp z
      (by simpa only [he0] using hφ.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,hφD]
    apply ContinuousLinearMap.ext
    intro d
    have H := congrArg (fun A : Model n →L[ℝ] ℝ => A d) Hc
    simpa only [neg_apply,ContinuousLinearMap.comp_apply,
      innerSL_apply_apply,inner_neg_left,neg_inj] using H.symm
  have hψval : uv.1 a=ψ z := by simpa only [ψ,he0] using hval
  have hψlo : ∀ᶠ w in 𝓝 z,ψ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w) := by
    have H := he.continuousAt.eventually (show ∀ᶠ v in 𝓝 (e z),φ v≤uv.1 (riemannianExp a v) by rwa [he0])
    filter_upwards [H,hei] with w hw hwi
    simpa only [ψ,hwi] using hw
  have Hpull (d : Model n) : fderiv ℝ (fderiv ℝ ψ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp a p))) z d d =
      fderiv ℝ (fderiv ℝ φ) 0 (fderiv ℝ e z d) (fderiv ℝ e z d)+
        hessianValue a p (fderiv ℝ e z d) := by
    have hzF : fderiv ℝ (fun v => φ v+c v) 0=0 := by
      rw [fderiv_fun_add (hφ.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
        hφD,(normalCost_hasFDerivAt_zero hp).fderiv]
      simp only [map_neg,add_neg_cancel]
    have HF := second_fderiv_comp_stationary (f := fun v => φ v+c v) (g := e)
      (he0.symm ▸ hφ.add hc) he2 (by rwa [he0]) d d
    rw [he0,second_fderiv_add_eq hφ hc] at HF
    rw [hessianValue_eq_normalHessian hp]
    have Heq : (fun w => ψ w+chartCost a (riemannianExp a p) w) =ᶠ[𝓝 z]
        (fun w => φ (e w)+c (e w)) := by
      filter_upwards [hce] with w hw
      rw [hw]
    have HH := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A d d) Heq.fderiv.fderiv_eq
    rw [second_fderiv_add_eq hψ hcc] at HH
    exact HH.trans HF
  have hψpos (d : Model n) : (m*k)*‖d‖^2≤fderiv ℝ (fderiv ℝ ψ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,L)))) z d d := by
    rw [hLb,Hpull]
    calc
      _ = m*(k*‖d‖^2) := by ring
      _ ≤ m*‖fderiv ℝ e z d‖^2 := mul_le_mul_of_nonneg_left (Hk d) hm.le
      _ ≤ _ := hpos _
  obtain ⟨w,hw⟩ := hsur d
  have HB := HC x0 uv huv ψ hψ hψD hψval hψlo hψpos w
  rw [hLb,Hpull,hw] at HB
  have Hb := Hk w
  rw [hw] at Hb
  calc
    _ ≤ C*‖w‖^2 := HB
    _ ≤ (C/k)*‖d‖^2 := by
      have HH : ‖w‖^2≤‖d‖^2/k := (le_div_iff₀ hk).mpr (by nlinarith only [Hb])
      convert! mul_le_mul_of_nonneg_left HH hC using 1; ring

end NormalRelativeHessianBound
end WeakMTWTransport

end

end

end

end OAI
