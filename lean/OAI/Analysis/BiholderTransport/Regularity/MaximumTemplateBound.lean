import Mathlib
import OAI.Analysis.BiholderTransport.Volume.OriginalNullSet
import OAI.Analysis.BiholderTransport.Regularity.MaximumSimultaneous
import OAI.Analysis.BiholderTransport.LinearAlgebra.FrameDeterminantClosure
import OAI.Analysis.BiholderTransport.Regularity.MaximumSelectionCompact
import OAI.Analysis.BiholderTransport.Regularity.OuterTemplatePrimitive
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterSign
import OAI.Analysis.BiholderTransport.Regularity.MaximumCenterLower
import OAI.Analysis.BiholderTransport.Regularity.MaximumLowerBound
import OAI.Analysis.BiholderTransport.Calculus.ScalarFamilyBounds

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric MeasureTheory
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumTemplateBound
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance templateDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance templateDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance templateBilinearGroup : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance templateBilinearSpace : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance

lemma WeakMTW.maximum_template_bound (hmtw:WeakMTW (n:=n) (M:=M))
    (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) :
    ∃B:ℝ,0 < B ∧ ∃eps:ℝ,0 < eps ∧
    ∀K eta:ℝ,1 ≤ K → 0 < eta → eta ≤ 1/128 →
    (let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
     eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) →
    ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀α D bm bp:ℝ,0 < D → 0 < bm → 0 < bp →
    bp/D*centerGamma ≤ 1 → bp/D*centerGamma/2 < eps →
    ∀C:ℝ,0 ≤ C →
      (∀s,|deriv (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) s| ≤ C) →
      bp/D*C ≤ 1/2 →
    (∀z:M,sectionOscillation uv.1 uv.2 z
      ((2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp) ≤ (1+eta)*D) →
    2*(2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp ≤ eta*D →
    MaximumFamily (n:=n) uv.2 α D bm bp centerTemplate
      (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) →
    (((1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)))^(n-1)*K/(8*centerGamma^2)) ≤ B := by
  classical
  have hgamma:=centerGamma_pos
  obtain ⟨c0,hc0,HG⟩:=exists_maximum_center_gain (n:=n) (M:=M)
  obtain ⟨χ,hχ,Hχ⟩:=exists_density_original_center_good (n:=n) (M:=M) hlam hcap
  obtain ⟨δ,hδ,Kd,hKd,U,hU,hU1,HS⟩:=hmtw.exists_maximum_simultaneous hn hlam (hlam.le.trans hcap)
  let a0:ℝ:=c0/(16*centerGamma)
  let μ:ℝ:=(1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ))
  have ha0:0 < a0:=by dsimp [a0]; positivity
  have hμ:0 < μ:=by dsimp [μ]; positivity
  obtain ⟨B,hB,HB⟩:=hmtw.frame_determinant_closure hμ ha0
    (show 0 < 3+9/(4*a0) by positivity) hχ hKd
  obtain ⟨eps,heps,HE⟩:=Metric.mem_nhds_iff.mp (Filter.Eventually.and (show ∀ᶠ l in 𝓝 (1:ℝ), l∈U from hU.mem_nhds hU1) HG)
  refine ⟨B,hB,eps,heps,?_⟩
  intro K eta hK heta heta1 hetasmall x0 uv huv α D bm bp hD hbm hbp hcenter hclose C hC hder houter hosc herror F
  let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
  let Bo:=outerTemplate M0 K eta
  let H:ℝ:=2*M0+8
  have hM:2 ≤ M0:=by dsimp [M0]; have hn0:=Nat.cast_nonneg (α:=ℝ) (Module.finrank ℝ (Model n)); linarith
  have hBo:ContDiff ℝ ∞ Bo:=outerTemplate_smooth _ _ _
  have hob (s):0 ≤ Bo s ∧ Bo s ≤ H:=⟨outerTemplate_nonneg hM hK heta heta1 hetasmall,
    outerTemplate_upper hM hK heta heta1 hetasmall⟩
  have hprof (s):centerTemplate s ≤ Bo s:=centerTemplate_le_outer hM hK heta heta1 hetasmall
  have hd:=densityDualClass_isDual huv
  let Lv:ℝ≥0:=⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  have hv:LipschitzWith Lv (uv.2:M → ℝ):=by
    rw [hd.2]
    exact cTransform_lipschitz uv.1.continuous (fun x y=>Metric.dist_le_diam_of_mem
      isCompact_univ.isBounded (mem_univ x) (mem_univ y))
  obtain ⟨A0,hA0⟩:=isCompact_univ.exists_bound_of_continuousOn uv.2.continuous.continuousOn
  have hrange:∀y:M,uv.2 y∈Icc (-A0) A0:=fun y=>abs_le.mp (hA0 y (mem_univ y))
  have hcsmall (b:ℝ) (hb:b∈Icc bm bp): b/D*(centerGamma/2) ≤ 1/2:=by
    have ht:=mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hb.2) centerGamma_pos.le
    nlinarith only [ht,hcenter]
  have hosmall (b:ℝ) (hb:b∈Icc bm bp):b/D*C ≤ 1/2:=
    (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hb.2) hC).trans houter
  have hmono (b:ℝ) (hb:b∈Icc bm bp):Monotone (fun s=>modifiedScalar α D centerTemplate (b,s)):=
    (modifiedScalar_strictMono centerTemplate_smooth (by positivity) hD (hbm.le.trans hb.1)
      (hcsmall b hb) exact_center_deriv_abs α).monotone
  have hmonoO (b:ℝ) (hb:b∈Icc bm bp):StrictMono (fun s=>modifiedScalar α D Bo (b,s)):=
    modifiedScalar_strictMono hBo hC hD (hbm.le.trans hb.1) (hosmall b hb) hder α
  have hLipφ (b:ℝ) (hb:b∈Icc bm bp):LipschitzWith 2 (fun s=>modifiedScalar α D centerTemplate (b,s)):=
    modifiedScalar_lipschitz centerTemplate_smooth (by positivity) hD (hbm.le.trans hb.1)
      (hcsmall b hb) exact_center_deriv_abs α
  have hLip (b:ℝ) (hb:b∈Icc bm bp):LipschitzWith (2*Lv) (modifiedDatum uv.2 α D b centerTemplate):=
    (hLipφ b hb).comp hv
  have hslope (b:ℝ) (hb:b∈Icc bm bp) (y:M):
      0 < deriv (fun s=>modifiedScalar α D centerTemplate (b,s)) (uv.2 y) ∧
      deriv (fun s=>modifiedScalar α D centerTemplate (b,s)) (uv.2 y)<1:=by
    refine ⟨lt_of_lt_of_le (by norm_num)
      (modifiedScalar_slope_bounds centerTemplate_smooth (by positivity) hD (hbm.le.trans hb.1)
        (hcsmall b hb) exact_center_deriv_abs α (uv.2 y)).1,?_⟩
    rw [modifiedScalar_deriv centerTemplate_smooth]
    have H:=mul_neg_of_pos_of_neg (div_pos (hbm.trans_le hb.1) hD) (centerTemplate_deriv_neg ((uv.2 y-α)/D))
    linarith only [H]
  obtain ⟨σ,hσ,β,hβmem,Q,hq,hβ,hQ⟩:=F.compact_subseq
  let F1:=F.comp σ hσ.tendsto_atTop
  let a:=Q.1
  let q:Model n:=Q.2
  let c:=riemannianExp a q
  obtain ⟨r0,hr0,N,hN,hNt,hgood⟩:=original_chart_good_null (Hχ x0 uv huv) uv.1.continuous hd c
  obtain ⟨k0,⟨J⟩⟩:=F1.eventually_jensen_first hmtw uv.1.continuous uv.2.continuous hd hBo.continuous
    (modifiedScalar_contDiff centerTemplate_smooth α D) hmono hLipφ hrange hQ hN
  let τ:ℕ → ℕ:=fun k=>k+k0
  have hτ:Tendsto τ atTop atTop:=tendsto_add_atTop_nat k0
  let F2:=F1.comp τ hτ
  have hQ2:Tendsto (fun k=>(F2.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)):=hQ.comp hτ
  have hβ2:Tendsto F2.b atTop (𝓝 β):=hβ.comp hτ
  let l:=deriv (fun s=>modifiedScalar α D centerTemplate (β,s)) (uv.2 c)
  let kc:=iteratedDeriv 2 (fun s=>modifiedScalar α D centerTemplate (β,s)) (uv.2 c)
  have hjcenter:=J.center_limit_positive hbm.le hbp (fun s=>(hob s).1) centerTemplate_smooth.continuous rfl hQ2
  have hcentβ:β/D*centerGamma ≤ 1:=
    (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hβmem.2) centerGamma_pos.le).trans hcenter
  obtain ⟨hlhalf,hl1,hkc,hkc1,hkc2⟩:=exact_center_slope_curvature hD (hbm.trans_le hβmem.1) hcentβ
    (lt_of_lt_of_le (by norm_num) hjcenter)
  change -kc / l^2 ≤ 4*centerGamma*(1-l)/D at hkc2
  have hl:0 < l:=lt_of_lt_of_le (by norm_num) hlhalf
  have hldist:dist l 1 < eps:=by
    rw [Real.dist_eq]
    apply exact_center_slope_small hD (hbm.le.trans hβmem.1)
    have h:=mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hβmem.2) centerGamma_pos.le
    exact (div_le_div_of_nonneg_right h (by norm_num)).trans_lt hclose
  obtain ⟨hlU,hgain⟩:=HE (show l∈ball 1 eps from hldist)
  have hH:=hgain hl hl1 hmtw uv.1 uv.2 uv.1.continuous Lv hv hd α D bm bp centerTemplate Bo
    hBo.continuous centerTemplate_smooth hmono (2*Lv) hLip F2 a c N J q β hq rfl hQ2 hβ2 rfl
  have hqa:2*(-(kc/l^2))*a0*D ≤ c0*(1-l):=by
    have H:=mul_le_mul_of_nonneg_right hkc2 (show 0 ≤ 2*a0*D by positivity)
    have he:(4*centerGamma*(1-l)/D)*(2*a0*D)=c0*(1-l)/2:=by
      dsimp only [a0]
      field_simp [hD.ne', centerGamma_pos.ne']
      ring
    rw [he] at H
    have hpos:0 ≤ c0*(1-l):=mul_nonneg hc0.le (sub_nonneg.mpr hl1.le)
    calc
      2*(-(kc/l^2))*a0*D = (-kc/l^2)*(2*a0*D) := by ring
      _ ≤ c0*(1-l)/2 := H
      _ ≤ c0*(1-l) := by linarith only [hpos]
  have hmargin (s:ℝ) (hs:-2*eta ≤ s) (hs':s ≤ 1-eta) (hsM:Bo s ≤ M0):
      1 < deriv (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s) ∧
      iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s)<0:=by
    have he:(α+D*s-α)/D=s:=by field_simp [hD.ne']; ring
    have hh:=exact_outer_slope_curvature hM hK heta hD (hbm.trans_le hβmem.1) hC hder
      (hosmall β hβmem) (by rwa [he]) (by rwa [he]) (by rwa [he])
    exact ⟨hh.1,hh.2.2.1⟩
  have hHeq:H+2=2*M0+10:=by dsimp [H]; ring
  have herr (k):2*(H+2)*F2.b k ≤ eta*D:=by
    have hh:=mul_le_mul_of_nonneg_left (F2.parameter k).2.le (show 0 ≤ 2*(H+2) by dsimp [H,M0]; positivity)
    apply hh.trans
    simpa only [hHeq] using herror
  have hbk (k):0 < F2.b k:=hbm.trans (F2.parameter k).1
  have hosc2 (k):sectionOscillation uv.1 uv.2 (F2.row k).q.1.1 ((H+2)*F2.b k) ≤ (1+eta)*D:=by
    apply le_trans (sectionOscillation_mono uv.2.continuous hd _ (by have hb:=hbk k; dsimp [H,M0]; positivity)
      (mul_le_mul_of_nonneg_left (F2.parameter k).2.le (show 0 ≤ H+2 by dsimp [H,M0]; positivity)))
    simpa only [hHeq] using hosc (F2.row k).q.1.1
  obtain ⟨s,hs,r,m,L,CL,hCL,i,hr,hm,hL,hCLbd,hri,hmn,hmt,hbar,hmi,hsl,hsu,hcapO,e,t,he,ht,hriq,hqe,hqD,hgap⟩:=
    J.selected_pole_compact hlam (hlam.le.trans hcap) huv hBo hd hbm.le hbp hprof hob
      (fun s=>⟨(centerTemplate_bounds s).1.le,(centerTemplate_bounds s).2.le⟩)
      (fun s hs=>(centerTemplate_right hs).le) hβ2 hQ2
      (mul_pos hc0 (sub_pos.mpr hl1)) (div_neg_of_neg_of_pos hkc (sq_pos_of_pos hl)) hH
      hD ha0 hqa heta1 le_rfl le_rfl (by linarith only [heta1])
      (fun s hs=>outerTemplate_lower hM hK heta heta1 hetasmall hs.le) herr hosc2 hmonoO hmargin
  let J3:=J.comp s hs.tendsto_atTop
  let F3:=F2.comp s hs.tendsto_atTop
  obtain ⟨CH,hCH,hCHbd⟩:=eventual_lower_bound_of_center_gain (mul_pos hc0 (sub_pos.mpr hl1)).le
    (div_neg_of_neg_of_pos hkc (sq_pos_of_pos hl)).le hH
  let lo:=deriv (fun z=>modifiedScalar α D Bo (β,z)) (uv.2 (riemannianExp a (r i)))
  let ko:=iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (uv.2 (riemannianExp a (r i)))
  obtain ⟨hlo,hlo2,hko,hko1⟩:=exact_outer_slope_curvature hM hK heta hD
    (hbm.trans_le hβmem.1) hC hder (hosmall β hβmem) hsl hsu hcapO
  obtain ⟨rc,hrc,hrev,V,W,hVs,hVp,hWs,hWp,hσc,hdc,hdo,hdet⟩:=HS x0 uv huv Lv hv hd α D bm bp
    (-A0) A0 centerTemplate Bo hBo.continuous centerTemplate_smooth hBo hmono hmonoO hrange hslope
    (2*Lv) hLip F3 a c χ N r0 hχ hr0 hgood J3 q β l kc hq rfl
    (hQ2.comp hs.tendsto_atTop) (hβ2.comp hs.tendsto_atTop) rfl rfl hlU hl hl1 hkc
    r m L hr hm hL CH CL hCH hCL (hs.tendsto_atTop.eventually hCHbd) hCLbd i (hri i)
    (hμ.trans_le hmi) e t lo ko he ht hriq hqe rfl rfl hlo hko
  have hVdet:0 < (bilinearOperator V).det:=symmetric_det_pos (bilinearOperator_symmetric hVs) (by
    intro d hd; simpa only [bilinearOperator_inner] using hVp d hd)
  have hWdet:0 < (bilinearOperator W).det:=symmetric_det_pos (bilinearOperator_symmetric hWs) (by
    intro d hd; simpa only [bilinearOperator_inner] using hWp d hd)
  have hgainDet:=scalar_determinant_gain hμ hmi (zero_lt_one.trans_le hK) centerGamma_pos
    (hbm.trans_le hβmem.1) hD hVdet.le hWdet.le hkc1 hko1 hdet
  exact HB _ a c (fun j=>(show TangentSpace 𝓘(ℝ,Model n) a from r j)) m q hmn hmt hri hbar
    i e t D l lo hmi he ht hD hqe hqD hgap hriq ⟨hlhalf,hl1.le⟩ hl1 ⟨hlo.le,hlo2⟩ hlo rc hrc hrev
    (bilinearOperator V).det (bilinearOperator W).det (μ^(n-1)*K/(8*centerGamma^2)) hWdet
    (by positivity) hdc hdo hgainDet

end MaximumTemplateBound
end WeakMTWTransport

end
end

end OAI
