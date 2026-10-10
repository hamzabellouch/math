import Mathlib
import OAI.Analysis.BiholderTransport.Volume.UniformCharts
import OAI.Analysis.BiholderTransport.Regularity.PullbackDet
import OAI.Analysis.BiholderTransport.Coordinates.NormalTestChart
import OAI.Analysis.BiholderTransport.Regularity.MixedDetIntrinsic
import OAI.Analysis.BiholderTransport.Regularity.UniformTestDet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction NNReal

namespace WeakMTWTransport
section IntrinsicTestDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance ivFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma WeakMTW.exists_uniform_intrinsic_test_det_bound
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ}
    (hlam:0<lam) (hcap:0≤cap) :
    ∃ K:ℝ,0<K ∧ ∀ (x0 x:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ))
      (p:TangentSpace 𝓘(ℝ,Model n) x) (φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → p∈injectivityDomain x →
      ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p →
      uv.1 x=φ 0 → (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp x w)) →
      (∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) →
      expJacobian (n:=n) x p *
        |(bilinearOperator (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).det|≤K := by
  obtain ⟨C,hC,l,u,hl,hu,Hcharts⟩:=exists_uniform_volume_charts (n:=n) (M:=M)
  let A:ℝ:=(cap/lam)*((C:ℝ)*(C:ℝ))^n
  have hA:0≤A:=by dsimp [A]; positivity
  refine ⟨u*A/l+1,by positivity,?_⟩
  intro x0 x uv p φ huv hp hφ hφD hval hlo hpos
  let y:=riemannianExp (n:=n) x p
  obtain ⟨a,U,hU,hxU,hUa,hCa,hDa,hJa⟩:=Hcharts x
  obtain ⟨b,V,hV,hyV,hVb,hCb,hDb,hJb⟩:=Hcharts y
  have hx:=hUa hxU
  have hy:=hVb hyV
  let z:=extChartAt 𝓘(ℝ,Model n) a x
  obtain ⟨ψ,R,hψ,hreg,hey,hvalue,hlower,hpositive,hR,hpull⟩:=
    normal_test_to_chart hx hp hφ hφD hval hlo hpos
  have Hbound:|(fderiv ℝ (chartTestContact a b ψ) z).det|≤A:=by
    apply hmtw.test_det_bound_on_charts hlam hcap hU hUa hV hVb hDa hCb
      (mem_image_of_mem _ hxU) huv hψ (by rwa [hey]) hreg hvalue hlower
    simpa only [hey] using hpositive
  let W:=bilinearOperator (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)
  let B:=mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b y)
  let T:=fderiv ℝ (chartTestContact a b ψ) z
  have hfactor:(R.adjoint.comp (W.comp R))=B.comp T:=by
    rw [←hpull]
    have H:=relative_hessian_operator_factor_fixed ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)
      hψ hreg (by rwa [hey])
    simpa only [hey] using H
  have Hdet:R.toLinearMap.normDet^2* |W.det|=|B.det| * |T.det|:=by
    rw [←abs_det_hessian_pullback R W rfl,hfactor]
    change |(B.toLinearMap.comp T.toLinearMap).det|=_
    rw [LinearMap.det_comp,abs_mul]
  have Hmix:chartJacobian (n:=n) a x * |B.det| *
      (chartJacobian (n:=n) b y*expJacobian (n:=n) x p)=1:=mixed_intrinsic_det hx hp hy
  have Heq:chartJacobian (n:=n) b y*expJacobian (n:=n) x p* |W.det|=
      chartJacobian (n:=n) a x* |T.det|:=by
    calc
      _ = (chartJacobian (n:=n) a x*R.toLinearMap.normDet)^2*
          (chartJacobian (n:=n) b y*expJacobian (n:=n) x p* |W.det|):=by rw [hR]; ring
      _ = (chartJacobian (n:=n) a x)^2*(chartJacobian (n:=n) b y*expJacobian (n:=n) x p)*
          (R.toLinearMap.normDet^2* |W.det|):=by ring
      _ = (chartJacobian (n:=n) a x)^2*(chartJacobian (n:=n) b y*expJacobian (n:=n) x p)*
          (|B.det| * |T.det|):=by rw [Hdet]
      _ = chartJacobian (n:=n) a x*(chartJacobian (n:=n) a x* |B.det| *
          (chartJacobian (n:=n) b y*expJacobian (n:=n) x p))* |T.det|:=by ring
      _ = _:=by rw [Hmix]; ring
  have Hlo:l*(expJacobian (n:=n) x p* |W.det|)≤
      chartJacobian (n:=n) b y*expJacobian (n:=n) x p* |W.det|:=by
    nlinarith only [mul_le_mul_of_nonneg_right (hJb y hyV).1
      (mul_nonneg (expJacobian_pos_of_injectivityDomain hp).le (abs_nonneg W.det))]
  have Hhi:chartJacobian (n:=n) a x* |T.det|≤u*A:=
    mul_le_mul (hJa x hxU).2 Hbound (abs_nonneg _) hu.le
  have H:expJacobian (n:=n) x p* |W.det|≤u*A/l:=
    (le_div_iff₀ hl).mpr (by nlinarith only [Hlo,Heq,Hhi])
  exact H.trans (by linarith)

end IntrinsicTestDet
end WeakMTWTransport

end
end

end OAI
