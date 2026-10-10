import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.CurvatureBounds

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma CurvatureBound.taylor {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (x v : U) :
    ‖f (x+v)-f x-fderiv ℝ f x v‖≤H*‖v‖^2 := by
  let q : ℕ → W := fun n => (2:ℝ)^n • (f (x+(1/2:ℝ)^n • v)-f x)
  have hD : HasDerivAt (fun t : ℝ => f (x+t • v)) (fderiv ℝ f x v) 0 := by
    have hd := (hf (x+(0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v))
    simpa only [zero_smul,add_zero,one_smul,zero_add,Function.comp_def,Pi.add_apply,id_eq] using hd
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall (fun n => by simp only [mem_Ioi]; positivity)⟩
  have hq : Tendsto q atTop (𝓝 (fderiv ℝ f x v)) := by
    simpa [Function.comp_def,q,← inv_pow] using hD.tendsto_slope_zero_right.comp hp
  have hb (n : ℕ) : dist (q n) (q (n+1))≤(H*‖v‖^2/2)*(1/2:ℝ)^n := by
    let r : ℝ := (1/2:ℝ)^n
    have hr : 0≤r := by dsimp [r]; positivity
    have hn : 0≤(2:ℝ)^n := by positivity
    have hinv : (2:ℝ)^n*r=1 := by dsimp [r]; rw [← mul_pow]; norm_num
    have hcent := hc (x+(r/2) • v) ((r/2) • v)
    rw [show (x+(r/2) • v)+(r/2) • v=x+r • v by module,
      show (x+(r/2) • v)-(r/2) • v=x by module,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0≤r/2)] at hcent
    have he : q n-q (n+1)=(2:ℝ)^n • (f (x+r • v)+f x-(2:ℝ) • f (x+(r/2) • v)) := by
      dsimp only [q]
      rw [pow_succ,pow_succ]
      change (2:ℝ)^n • (f (x+r • v)-f x)-((2:ℝ)^n*2) • (f (x+(r*(1/2)) • v)-f x)=_
      rw [show r*(1/2)=r/2 by ring]
      module
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hn]
    apply (mul_le_mul_of_nonneg_left hcent hn).trans
    have heq : (2:ℝ)^n*(H*(r/2*‖v‖)^2)=(H*‖v‖^2/4)*r := by
      calc
        _ = (H*‖v‖^2/4)*((2:ℝ)^n*r)*r := by ring
        _ = _ := by rw [hinv]; ring
    rw [heq]
    change (H*‖v‖^2/4)*r≤(H*‖v‖^2/2)*r
    gcongr
    nlinarith [mul_nonneg hH (sq_nonneg ‖v‖)]
  have hh := dist_le_of_le_geometric_of_tendsto₀ (r:=(1/2:ℝ)) (C:=H*‖v‖^2/2) (by norm_num) hb hq
  simpa only [q,pow_zero,one_smul,dist_eq_norm,show (H*‖v‖^2/2)/(1-(1/2:ℝ))=H*‖v‖^2 by ring] using hh

lemma fderiv_bound_of_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H ε δ : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (hb : ∀ x, ‖f x‖≤ε) (hε : 0≤ε) (hδ : 0<δ) (x : U) :
    ‖fderiv ℝ f x‖≤2*ε/δ+H*δ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hv' : ‖v‖≤1 := hv.le
  have ht := hc.taylor hH hf x (δ • v)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,map_smul] at ht
  have hb' : ‖f (x+δ • v)-f x‖≤2*ε := (norm_sub_le _ _).trans (by linarith [hb (x+δ • v),hb x])
  have hD : δ*‖fderiv ℝ f x v‖≤2*ε+H*δ^2 := by
    have hh := norm_sub_le (f (x+δ • v)-f x) (f (x+δ • v)-f x-δ • fderiv ℝ f x v)
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hδ] at hh
    have hv2 : ‖v‖^2≤1 := by nlinarith [norm_nonneg v]
    nlinarith [mul_le_mul_of_nonneg_left hv2 (show 0≤H*δ^2 by positivity)]
  have hD' : ‖fderiv ℝ f x v‖≤2*ε/δ+H*δ := by
    have hD' : ‖fderiv ℝ f x v‖≤(2*ε+H*δ^2)/δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith [hD])
    convert hD' using 1
    field_simp
  simpa only [div_one] using hD'

lemma fderiv_difference_bound_of_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H ε δ : ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfc : CurvatureBound f H) (hgc : CurvatureBound g H) (hH : 0≤H)
    (hfg : ∀ x, ‖f x-g x‖≤ε) (hε : 0≤ε) (hδ : 0<δ) (x : U) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖≤2*ε/δ+2*H*δ := by
  have hb := fderiv_bound_of_curvature (hfc.sub hgc) (add_nonneg hH hH) (hf.sub hg) hfg hε hδ x
  change ‖fderiv ℝ (f-g) x‖≤_ at hb
  rwa [fderiv_sub (hf x) (hg x),← two_mul H] at hb

lemma uniform_spatial_derivative_limit {X U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → X × U → W} {f : X × U → W} {S : Set X} {H : ℝ} (hH : 0≤H)
    (hF : ∀ n, ∀ t∈S, Differentiable ℝ (fun x => F n (t,x)))
    (hc : ∀ n, ∀ t∈S, CurvatureBound (fun x => F n (t,x)) H)
    (hlim : TendstoUniformlyOn F f atTop {p | p.1∈S}) :
    ∃ D : X × U → (U →L[ℝ] W),
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2) D atTop {p | p.1∈S} ∧
      ∀ t∈S, ∀ x, HasFDerivAt (fun x => f (t,x)) (D (t,x)) x := by
  let DF : ℕ → X × U → (U →L[ℝ] W) := fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2
  have huc : UniformCauchySeqOn DF atTop {p | p.1∈S} := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let δ := ε/(8*(H+1))
    let η := ε*δ/8
    have hδ : 0<δ := by dsimp [δ]; positivity
    have hη : 0<η := by dsimp [η]; positivity
    obtain ⟨K,hK⟩ := Metric.uniformCauchySeqOn_iff.mp hlim.uniformCauchySeqOn η hη
    refine ⟨K,?_⟩
    intro m hm n hn p hp
    have hh := fderiv_difference_bound_of_curvature (hF m p.1 hp) (hF n p.1 hp)
      (hc m p.1 hp) (hc n p.1 hp) hH
      (fun x => (show ‖F m (p.1,x)-F n (p.1,x)‖<η by simpa only [dist_eq_norm] using hK m hm n hn (p.1,x) hp).le)
      hη.le hδ p.2
    rw [dist_eq_norm]
    apply hh.trans_lt
    have hd : δ*(8*(H+1))=ε := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
    have he : 2*η/δ=ε/4 := by dsimp [η]; field_simp; ring
    rw [he]
    nlinarith [mul_nonneg hH hδ.le]
  have hpoint (p : X × U) : ∃ a : U →L[ℝ] W, p.1∈S → Tendsto (fun n => DF n p) atTop (𝓝 a) := by
    by_cases hp : p.1∈S
    · obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (huc.cauchySeq hp)
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun h => (hp h).elim⟩
  choose D hD using hpoint
  have hdlim := huc.tendstoUniformlyOn_of_tendsto (fun p hp => hD p hp)
  refine ⟨D,hdlim,?_⟩
  intro t ht x
  have hds : TendstoUniformly (fun n x => DF n (t,x)) (fun x => D (t,x)) atTop := by
    simpa only [Function.comp_def,preimage_ofPred_eq,ht,ofPred_true,tendstoUniformlyOn_univ] using hdlim.comp (fun x : U => (t,x))
  exact hasFDerivAt_of_tendstoUniformly hds (fun n x => (hF n t ht x).hasFDerivAt)
    (fun x => hlim.tendsto_at (x:=(t,x)) ht) x

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

lemma contDiff_fderiv_slice {A U W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : A × U → W} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : A × U => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he (p : A × U) : fderiv ℝ (fun x => F (p.1,x)) p.2 =
      (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ A U) := by
    have hin : HasFDerivAt (fun x : U => (p.1,x)) (ContinuousLinearMap.inr ℝ A U) p.2 := by
      convert (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1 <;> rfl
    exact ((hF.differentiable (by simp) p).hasFDerivAt.comp p.2 hin).fderiv
  simp_rw [he]
  exact (hF.fderiv_right (m:=∞) (by simp)).clm_comp contDiff_const

lemma smooth_spatial_limit_nat {A U : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup U] [NormedSpace ℝ U] (k : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : ℕ → A × U → W} {f : A × U → W} {S : Set A},
      (∀ n, ContDiff ℝ ∞ (F n)) →
      (∀ j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈S → ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => F n (t,y)) x‖≤C) →
      TendstoUniformlyOn F f atTop {p | p.1∈S} →
      (∀ t∈S, ContDiff ℝ k (fun x => f (t,x))) ∧
      ContinuousOn (fun p : A × U => iteratedFDeriv ℝ k (fun x => f (p.1,x)) p.2) {p | p.1∈S} ∧
      TendstoUniformlyOn (fun n (p : A × U) => iteratedFDeriv ℝ k (fun x => F n (p.1,x)) p.2)
        (fun p : A × U => iteratedFDeriv ℝ k (fun x => f (p.1,x)) p.2) atTop {p | p.1∈S} := by
  induction k with
  | zero =>
    intro W _ _ _ F f S hF hb hl
    have hc : ContinuousOn f {p | p.1∈S} := hl.continuousOn
      (Frequently.of_forall fun n => (hF n).continuous.continuousOn)
    refine ⟨fun t ht => contDiff_zero.mpr (hc.comp_continuous
      (continuous_const.prodMk continuous_id) (fun x => ht)),?_,?_⟩
    · simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryFin0 ℝ U W).symm.continuous.comp_continuousOn hc
    · simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryFin0 ℝ U W).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn hl
  | succ k ih =>
    intro W _ _ _ F f S hF hb hl
    obtain ⟨C,hC,hCb⟩ := hb 2
    obtain ⟨D,hD,hd⟩ := uniform_spatial_derivative_limit (by positivity : 0≤2*C)
      (fun n t ht => ((hF n).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
      (fun n t ht => curvature_of_second_derivative_bound
        ((hF n).comp (contDiff_const.prodMk contDiff_id)) hC (hCb n t ht)) hl
    let DF : ℕ → A × U → (U →L[ℝ] W) := fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2
    let df : A × U → (U →L[ℝ] W) := fun p => fderiv ℝ (fun x => f (p.1,x)) p.2
    have hdl : TendstoUniformlyOn DF df atTop {p | p.1∈S} :=
      hD.congr_right (fun p hp => (hd p.1 hp p.2).fderiv.symm)
    have hdb : ∀ j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈S → ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => DF n (t,y)) x‖≤C := by
      intro j
      obtain ⟨C,hC,hCb⟩ := hb (j+1)
      exact ⟨C,hC,fun n t ht x => by simpa only [DF,norm_iteratedFDeriv_fderiv] using hCb n t ht x⟩
    obtain ⟨hsc,hjc,hjl⟩ := ih (fun n => contDiff_fderiv_slice (hF n)) hdb hdl
    refine ⟨?_,?_,?_⟩
    · intro t ht
      rw [show (↑(k+1) : ℕ∞ω)=↑k+1 by simp,contDiff_succ_iff_fderiv]
      exact ⟨fun x => (hd t ht x).differentiableAt,by simp,hsc t ht⟩
    · simpa only [df,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryRightEquiv' ℝ k U W).symm.continuous.comp_continuousOn hjc
    · simpa only [DF,df,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryRightEquiv' ℝ k U W).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn hjl

end RVM

end

end OAI
