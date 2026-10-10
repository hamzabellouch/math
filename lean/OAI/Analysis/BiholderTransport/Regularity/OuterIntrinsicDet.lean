import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.FixedJoinSpectrum
import OAI.Analysis.BiholderTransport.Calculus.ScalarInverseJet
import OAI.Analysis.BiholderTransport.LinearAlgebra.QuadraticTest
import OAI.Analysis.BiholderTransport.LinearAlgebra.BranchDividedBaseline
import OAI.Analysis.BiholderTransport.LinearAlgebra.Aggregate
import OAI.Analysis.BiholderTransport.Regularity.IntrinsicTestDet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterIntrinsicDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance oiFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma WeakMTW.exists_uniform_outer_normal_det_bound
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0≤cap) :
    ∃K:ℝ,0<K ∧ ∀ (a:M) (r:TangentSpace 𝓘(ℝ,Model n) a) (G:M×M → ℝ) (l:ℝ),
      r∈minimizingVectors a →
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (a,riemannianExp a r) →
      (∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
        (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
      ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.1 a) → HasDerivAt φ l (uv.1 a) → iteratedDeriv 2 φ (uv.1 a)≤0 →
      ∀H:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] ℝ,
      (∀d e,H d e=H e d) → (∀d,0≤H d d) →
      HasLowerSecondTaylor (fun w=>φ (uv.1 (riemannianExp a w))+
        G (riemannianExp a w,riemannianExp a r)) 0 H →
      ∃V:TangentSpace 𝓘(ℝ,Model n) a →L[ℝ] TangentSpace 𝓘(ℝ,Model n) a,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,inner ℝ (V d) d=H d d+
          (l*hessianValue a (l⁻¹ • r) d-
            fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp a w,riemannianExp a r))) 0 d d)-
          (iteratedDeriv 2 φ (uv.1 a)/l^2)*(inner ℝ r d)^2) ∧
        expJacobian (n:=n) a (l⁻¹ • r)*V.det≤l^n*K := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_intrinsic_test_det_bound hlam hcap
  refine ⟨K,hK,?_⟩
  intro a r G l hr hG hagree hl x0 uv φ huv hmono hφ hd hconc H hHs hH hjet
  let E:=TangentSpace 𝓘(ℝ,Model n) a
  let c:E → ℝ:=fun w=>G (riemannianExp a w,riemannianExp a r)
  have hlp:0<l:=zero_lt_one.trans hl
  have ht:0<l⁻¹:=inv_pos.mpr hlp
  have ht1:l⁻¹<1:=(inv_lt_one₀ hlp).mpr hl
  have hp:=contracted_minimizer_mem_injectivityDomain hr ht ht1
  obtain ⟨m,hm,Hm⟩:=exists_branch_divided_baseline hr ht ht1 hG hagree
  have hCJ:=cost_branch_normal_jets (r:=r) (T:=(1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs=>contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have hc:ContDiffAt ℝ 2 c 0:=by
    have hh:ContDiffAt ℝ ∞ c 0:=by simpa only [c,one_smul] using hCJ.1
    exact hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcD:fderiv ℝ c 0=innerSL ℝ (-r):=by simpa only [c,one_smul] using hCJ.2.1.fderiv
  let I:E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  let R:E →L[ℝ] E →L[ℝ] ℝ:=(innerSL ℝ r).smulRight (innerSL ℝ r)
  let W:E →L[ℝ] E →L[ℝ] ℝ:=H+l • normalHessian a (l⁻¹ • r)-fderiv ℝ (fderiv ℝ c) 0-
    (iteratedDeriv 2 φ (uv.1 a)/l^2) • R
  have hdiag:∀d,W d d=H d d+(l*hessianValue a (l⁻¹ • r) d-
      fderiv ℝ (fderiv ℝ c) 0 d d)-(iteratedDeriv 2 φ (uv.1 a)/l^2)*(inner ℝ r d)^2:=by
    intro d
    simp only [W,R,sub_apply,add_apply,
      smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,
      innerSL_apply_apply,hessianValue_eq_normalHessian hp]
    ring
  have hWs:∀d e,W d e=W e d:=by
    intro d e
    simp only [W,R,sub_apply,add_apply,
      smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,
      innerSL_apply_apply,hHs d e,normalHessian_symm hp d e,
      (hc.isSymmSndFDerivAt (by norm_num)).eq d e]
    ring
  have hbase:∀d,m*‖d‖^2≤W d d:=by
    intro d
    have HB:=Hm d
    change m*‖d‖^2≤hessianValue a (l⁻¹ • r) d/l⁻¹-fderiv ℝ (fderiv ℝ c) 0 d d at HB
    rw [div_inv_eq_mul,mul_comm (hessianValue _ _ _)] at HB
    have hs:0≤-(iteratedDeriv 2 φ (uv.1 a)/l^2)*(inner ℝ r d)^2:=
      mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hconc (sq_nonneg _))) (sq_nonneg _)
    rw [hdiag]
    linarith only [HB,hH d,hs]
  let V:=bilinearOperator W
  have hVs:∀d e,inner ℝ (V d) e=inner ℝ d (V e):=bilinearOperator_symmetric hWs
  have hVp:∀d,d≠0 → 0 < inner ℝ (V d) d:=by
    intro d hd
    rw [show inner ℝ (V d) d=W d d from bilinearOperator_inner W d d]
    exact (mul_pos hm (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le (hbase d)
  refine ⟨V,hVs,hVp,?_,?_⟩
  · intro d
    exact (bilinearOperator_inner W d d).trans (hdiag d)
  have Hbound:∀ε:ℝ,0<ε → ε < m/2 →
      expJacobian (n:=n) a (l⁻¹ • r)* |(bilinearOperator (W-ε • I)).det|≤l^n*K:=by
    intro ε hε hεm
    obtain ⟨q,hq,hq0,hqD,hqlo,hqH⟩:=hjet.exists_smooth_minorant hε
    let F:E → ℝ:=fun w=>q w-c w
    have hF:ContDiffAt ℝ 2 F 0:=hq.sub hc
    have hF0:F 0=φ (uv.1 a):=by
      dsimp only [F,c]
      rw [hq0,riemannianExp_zero]
      ring
    have hFlo:∀ᶠ w in 𝓝 (0:E),F w≤φ (uv.1 (riemannianExp a w)):=by
      filter_upwards [hqlo] with w hw
      change q w≤φ (uv.1 (riemannianExp a w))+c w at hw
      dsimp only [F]
      linarith only [hw]
    have hFD:fderiv ℝ F 0=innerSL ℝ r:=by
      rw [show F=(fun w=>q w-c w) from rfl,
        fderiv_fun_sub (hq.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
        hqD,hcD,map_neg,zero_sub,neg_neg]
    obtain ⟨f,hf,hf0,hflo,hfD,hfH⟩:=scalar_inverse_lower_test
      (v:=fun w:E=>uv.1 (riemannianExp a w)) (x:=0) hmono
      (by simpa only [riemannianExp_zero] using hφ)
      (by simpa only [riemannianExp_zero] using hd) hlp.ne' hF
      (by simpa only [riemannianExp_zero] using hF0) hFlo
    have hfD':fderiv ℝ f 0=innerSL ℝ (l⁻¹ • r):=by rw [hfD,hFD,map_smul]
    let B:=fderiv ℝ (fderiv ℝ f) 0+normalHessian a (l⁻¹ • r)
    have Heq:∀d,l*(B d d)=W d d-ε*‖d‖^2:=by
      intro d
      simp only [B,add_apply]
      rw [hfH,show F=(fun w=>q w-c w) from rfl,second_fderiv_sub hq hc,hqH,hFD,hdiag,
        hessianValue_eq_normalHessian hp]
      simp only [riemannianExp_zero,innerSL_apply_apply]
      field_simp [hlp.ne']
      ring
    have hpos:∀d,(m/2/l)*‖d‖^2≤B d d:=by
      intro d
      apply (mul_le_mul_iff_right₀ hlp).mp
      rw [Heq]
      have he:l*((m/2/l)*‖d‖^2)=(m/2)*‖d‖^2:=by field_simp [hlp.ne']
      rw [he]
      nlinarith only [hbase d,mul_le_mul_of_nonneg_right hεm.le (sq_nonneg ‖d‖)]
    have Htest:=HK x0 a uv (l⁻¹ • r) f huv hp hf hfD'
      (by simpa only [riemannianExp_zero] using hf0.symm) hflo
      ⟨m/2/l,by positivity,by simpa only [B,add_apply,hessianValue_eq_normalHessian hp] using hpos⟩
    have Hop:bilinearOperator (W-ε • I)=l • bilinearOperator B:=by
      have HB:W-ε • I=l • B:=by
        apply symmetric_bilinear_eq_of_diagonal
        · intro d e
          change W d e-ε*inner ℝ d e=W e d-ε*inner ℝ e d
          rw [hWs,real_inner_comm d e]
        · intro d e
          simp only [B,add_apply,smul_apply,
            normalHessian_symm hp d e,(hf.isSymmSndFDerivAt (by norm_num)).eq d e]
        · intro d
          change W d d-ε*inner ℝ d d=l*B d d
          rw [real_inner_self_eq_norm_sq]
          exact (Heq d).symm
      rw [HB]
      ext d
      simp only [bilinearOperator,ContinuousLinearMap.comp_apply,smul_apply,map_smul]
    rw [Hop]
    change expJacobian (n:=n) a (l⁻¹ • r)* |(l • (bilinearOperator B).toLinearMap).det|≤_
    rw [LinearMap.det_smul,show Module.finrank ℝ E=n from tangent_finrank a,abs_mul,abs_of_pos (pow_pos hlp n)]
    nlinarith only [mul_le_mul_of_nonneg_left Htest (pow_pos hlp n).le]
  have hcont:Continuous (fun ε:ℝ=>expJacobian (n:=n) a (l⁻¹ • r)*
      |(bilinearOperator (W-ε • I)).det|):=by
    exact continuous_const.mul (continuous_linearized_det
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap W I)
  have hlim:= (hcont.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hz:W-(0:ℝ) • I=W:=by
    ext d e
    change W d e-0*inner ℝ d e=W d e
    ring
  have H:expJacobian (n:=n) a (l⁻¹ • r)* |V.det|≤l^n*K:=by
    apply le_of_tendsto (show Tendsto (fun ε:ℝ=>expJacobian (n:=n) a (l⁻¹ • r)*
      |(bilinearOperator (W-ε • I)).det|) (𝓝[>] 0) (𝓝 (expJacobian (n:=n) a (l⁻¹ • r)* |V.det|)) from
        by simpa only [hz,V] using hlim)
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ) < m/2 by positivity)).filter_mono nhdsWithin_le_nhds] with ε hε hεm
    exact Hbound ε hε hεm
  rw [abs_of_pos (symmetric_det_pos hVs hVp)] at H
  exact H

end OuterIntrinsicDet
end WeakMTWTransport

end
end

end OAI
