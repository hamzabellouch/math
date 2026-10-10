import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.NormLower
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateTrueLog
import OAI.Analysis.BiholderTransport.LinearAlgebra.BranchDividedBaseline

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section BranchChartBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma exists_branch_chart_baseline {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    {l:ℝ} (hl : 1<l) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let c := fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,riemannianExp a r)
    ContDiffAt ℝ 2 c z ∧
    ∃ L:Model n →L[ℝ] ℝ, fderiv ℝ c z= -l • L ∧
      chartGradientVector a z L∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      ∃ m>0,∀ d:Model n,m*‖d‖^2≤
        l*fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,L)))) z d d-
        fderiv ℝ (fderiv ℝ c) z d d := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let V := TangentSpace 𝓘(ℝ,Model n) a
  let c := fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,riemannianExp a r)
  let b := riemannianExp a (l⁻¹ • r)
  let cN : V → ℝ := fun v => G (riemannianExp a v,riemannianExp a r)
  let cT := normalCost a (l⁻¹ • r)
  have hlp : 0<l := zero_lt_one.trans hl
  have ht : 0<l⁻¹ := inv_pos.mpr hlp
  have ht1 : l⁻¹<1 := (inv_lt_one₀ hlp).mpr hl
  have hp := contracted_minimizer_mem_injectivityDomain hr ht ht1
  obtain ⟨m,hm,Hm⟩ := exists_branch_divided_baseline hr ht ht1 hG hagree
  have hCJ := cost_branch_normal_jets (r := r) (T := (1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs => contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have hcN : ContDiffAt ℝ 2 cN 0 := by
    have hh : ContDiffAt ℝ ∞ cN 0 := by simpa only [cN,one_smul] using hCJ.1
    exact hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcND : fderiv ℝ cN 0=innerSL ℝ (-r) := by simpa only [cN,one_smul] using hCJ.2.1.fderiv
  have hcT : ContDiffAt ℝ 2 cT 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
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
  have hce : c =ᶠ[𝓝 z] (fun w => cN (e w)) := by
    filter_upwards [hei] with w hw
    simp only [c,cN,hw]
  have hTe : chartCost a b =ᶠ[𝓝 z] (fun w => cT (e w)) := by
    filter_upwards [hei] with w hw
    simp only [cT,b,normalCost,chartCost,hw]
  have hc : ContDiffAt ℝ 2 c z := ((he0.symm ▸ hcN).comp z he2).congr_of_eventuallyEq hce
  have hT : ContDiffAt ℝ 2 (chartCost a b) z := ((he0.symm ▸ hcT).comp z he2).congr_of_eventuallyEq hTe
  have hstat : fderiv ℝ (fun v => l*cT v-cN v) 0=0 := by
    rw [fderiv_fun_sub ((hcT.differentiableAt (by norm_num)).const_mul _) (hcN.differentiableAt (by norm_num))]
    change fderiv ℝ (l • cT) 0-fderiv ℝ cN 0=0
    rw [fderiv_const_smul_field,Pi.smul_apply,hcND,(normalCost_hasFDerivAt_zero hp).fderiv]
    simp only [map_neg,map_smul,smul_neg,smul_smul,mul_inv_cancel₀ hlp.ne',one_smul,sub_self]
  have hstatC : fderiv ℝ (fun w => l*chartCost a b w-c w) z=0 := by
    have H : (fun w => l*chartCost a b w-c w)=ᶠ[𝓝 z] (fun w => l*cT (e w)-cN (e w)) := by
      filter_upwards [hTe,hce] with w hw hw'
      rw [hw,hw']
    rw [H.fderiv_eq,fderiv_fun_comp z (g := fun v:V => l*cT v-cN v)
      (by simpa only [he0] using (((contDiffAt_const (c := l)).mul hcT).sub hcN).differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,hstat,ContinuousLinearMap.zero_comp]
  have hcD : fderiv ℝ c z= -l • L := by
    rw [fderiv_fun_sub ((hT.differentiableAt (by norm_num)).const_mul _) (hc.differentiableAt (by norm_num))] at hstatC
    change fderiv ℝ (l • chartCost a b) z-fderiv ℝ c z=0 at hstatC
    rw [fderiv_const_smul_field,Pi.smul_apply,hLD.fderiv] at hstatC
    calc
      _ = l • (-L) := (sub_eq_zero.mp hstatC).symm
      _ = -l • L := by ext d; simp only [smul_apply,neg_apply,smul_eq_mul,mul_neg,neg_mul]
  refine ⟨hc,L,hcD,hLreg,m*k,mul_pos hm hk,?_⟩
  intro d
  have HF := second_fderiv_comp_stationary (f := fun v => l*cT v-cN v) (g := e)
    (he0.symm ▸ (contDiffAt_const.mul hcT).sub hcN) he2 (by rwa [he0]) d d
  rw [he0,second_fderiv_sub (contDiffAt_const.mul hcT) hcN,second_fderiv_const_mul] at HF
  have H : (fun w => l*chartCost a b w-c w)=ᶠ[𝓝 z] (fun w => l*cT (e w)-cN (e w)) := by
    filter_upwards [hTe,hce] with w hw hw'
    rw [hw,hw']
  have HH := congrArg (fun A:Model n →L[ℝ] Model n →L[ℝ] ℝ => A d d) H.fderiv.fderiv_eq
  rw [second_fderiv_sub (contDiffAt_const.mul hT) hc,second_fderiv_const_mul] at HH
  rw [hLb,HH,HF]
  have Hb := Hm (fderiv ℝ e z d)
  rw [hessianValue_eq_normalHessian hp] at Hb
  change m*‖fderiv ℝ e z d‖^2≤
    fderiv ℝ (fderiv ℝ cT) 0 (fderiv ℝ e z d) (fderiv ℝ e z d)/l⁻¹-
      fderiv ℝ (fderiv ℝ cN) 0 (fderiv ℝ e z d) (fderiv ℝ e z d) at Hb
  rw [div_inv_eq_mul] at Hb
  nlinarith only [Hb,mul_le_mul_of_nonneg_left (Hk d) hm.le]

end BranchChartBaseline
end WeakMTWTransport

end

end

end

end OAI
