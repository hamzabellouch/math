import Mathlib
import OAI.Probability.SKValue.Control.Regularity
import OAI.Probability.SKValue.Gaussian.SplitShape
import OAI.Probability.SKValue.Gaussian.ProfileLawStability

namespace OAI

section
open Filter Set
open scoped Topology
namespace SKValue
noncomputable def uniformDistance {A:Type*} (f g:A → ℝ) : ℝ := sSup (range (fun x ↦ |f x-g x|))
lemma uniformDistance_le {A:Type*} [Nonempty A] {f g:A → ℝ} {C:ℝ}
    (h:∀ x,|f x-g x| ≤ C) : uniformDistance f g ≤ C :=
  csSup_le (range_nonempty _) (by rintro _ ⟨x,rfl⟩;exact h x)
lemma le_uniformDistance {A:Type*} {f g:A → ℝ}
    (h:∃ C:ℝ,∀ x,|f x-g x| ≤ C) (x:A) : |f x-g x| ≤ uniformDistance f g := by
  apply le_csSup _ (mem_range_self x)
  obtain ⟨C,hC⟩:=h
  exact ⟨C,by rintro _ ⟨x,rfl⟩;exact hC x⟩
lemma uniformDistance_nonneg {A:Type*} [Nonempty A] {f g:A → ℝ}
    (h:∃ C:ℝ,∀ x,|f x-g x| ≤ C) : 0 ≤ uniformDistance f g := by
  obtain ⟨x⟩:=(inferInstance : Nonempty A)
  exact (abs_nonneg _).trans (le_uniformDistance h x)
lemma uniformDistance_tendsto {A:Type*} [Nonempty A] {F:ℕ → A → ℝ} {f:A → ℝ}
    (h:TendstoUniformly F f atTop) (hb:∀ n,∃ C:ℝ,∀ x,|F n x-f x| ≤ C) :
    Tendsto (fun n ↦ uniformDistance (F n) f) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩:=eventually_atTop.mp ((Metric.tendstoUniformly_iff.mp h) (ε/2) (half_pos hε))
  refine ⟨N,fun n hn ↦ ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (uniformDistance_nonneg (hb n))]
  apply (uniformDistance_le (C:=ε/2) (fun x ↦ ?_)).trans_lt (half_lt_self hε)
  have hx:=hN n hn x
  rw [Real.dist_eq,abs_sub_comm] at hx
  exact hx.le
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue
lemma OrderParameter.splitPrefix_integral_error (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    |(∫ s in (0:ℝ)..t,γ.coeff s)-(∫ s in (0:ℝ)..t,profileCoeff (γ.splitSegment 0 t t.property.1.le n) s)| ≤ γ.splitError t n := by
  have he:(∫ s in (0:ℝ)..t,γ.coeff s)=∫ s in (0:ℝ)..t,γ.cutoff s := by
    apply intervalIntegral.integral_congr_Ioo_of_le t.property.1.le
    intro s hs
    simp only [OrderParameter.cutoff,indicator_of_mem (show s∈Ico (0:ℝ) 1 from ⟨hs.1.le,hs.2.trans t.property.2⟩)]
  have hb:(∫ s in (0:ℝ)..t,profileCoeff (γ.splitSegment 0 t t.property.1.le n) s)=∫ s in (0:ℝ)..t,profileCoeff (γ.splitGrid t n) s := by
    apply intervalIntegral.integral_congr_Ioo_of_le t.property.1.le
    intro s hs
    exact (profileCoeff_append_before _ _ ⟨hs.1,by simpa only [γ.splitSegment_time,sub_zero] using hs.2.le⟩).symm
  have hp:IntervalIntegrable (profileCoeff (γ.splitGrid t n)) volume 0 1 := by
    simpa only [γ.splitGrid_time] using profileCoeff_integrable (γ.splitGrid t n)
  have hsub:uIcc (0:ℝ) (t:ℝ) ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl t.property.2.le
  rw [he,hb,←intervalIntegral.integral_sub γ.cutoff_integrable.intervalIntegrable (hp.mono_set hsub)]
  apply (intervalIntegral.abs_integral_le_integral_abs t.property.1.le).trans
  have hei:(∫ s in (0:ℝ)..t,|γ.cutoff s-profileCoeff (γ.splitGrid t n) s|)=
      ∫ s in (0:ℝ)..t,|profileCoeff (γ.splitGrid t n) s-γ.cutoff s| := by
    congr 1;funext s;exact abs_sub_comm _ _
  rw [hei]
  exact intervalIntegral.integral_mono_interval le_rfl t.property.1.le t.property.2.le
    (Eventually.of_forall (fun _ ↦ abs_nonneg _)) (hp.sub γ.cutoff_integrable.intervalIntegrable).abs
lemma OrderParameter.splitPrefix_integral_tendsto (γ:OrderParameter) (t:Ioo (0:ℝ) 1) :
    Tendsto (fun n ↦ (∫ s in (0:ℝ)..t,γ.coeff s)-(∫ s in (0:ℝ)..t,profileCoeff (γ.splitSegment 0 t t.property.1.le n) s)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n ↦ ?_) (γ.splitError_tendsto t)
  rw [Real.norm_eq_abs]
  exact γ.splitPrefix_integral_error t n

lemma IsDiffusion.splitResponse_tendsto {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) (t:Ioo (0:ℝ) 1) {f:ℝ → ℝ} (hf:BoundedSmooth f) :
    Tendsto (fun n ↦ profileResponse (splitTerminal γ t n) f (γ.splitSegment 0 t t.property.1.le n) 0 0)
      atTop (𝓝 (MeasureTheory.integral W.μ (fun z ↦ f (X t z)))) := by
  let : Nonempty (Icc (0:ℝ) (t:ℝ)×ℝ) := ⟨(⟨0,⟨le_rfl,t.property.1.le⟩⟩,0)⟩
  let F:=fun n (p:Icc (0:ℝ) (t:ℝ)×ℝ) ↦ deriv (splitSmooth γ t n p.1) p.2
  let g:=fun (p:Icc (0:ℝ) (t:ℝ)×ℝ) ↦ gradient W γ p.1 p.2
  let e:=fun n ↦ uniformDistance (F n) g
  obtain ⟨C,hC,hCb⟩:=splitSmooth_bulk_jets γ t ⟨t.property.1.le,t.property.2⟩ 0
  have hb:∀ n,∃ D:ℝ,∀ p:Icc (0:ℝ) (t:ℝ)×ℝ,|F n p-g p| ≤ D := by
    intro n;refine ⟨C+1,fun p ↦ ?_⟩
    exact (abs_sub _ _).trans (add_le_add (hCb n p.1 p.1.property 0 le_rfl p.2)
      (gradient_bound W γ ⟨p.1.property.1,p.1.property.2.trans t.property.2.le⟩ p.2))
  have hel:Tendsto e atTop (𝓝 0) := uniformDistance_tendsto
    (by simpa only [iteratedDeriv_one,F,g,gradient] using splitSmooth_jet_limits W γ t ⟨t.property.1.le,t.property.2⟩ 1) hb
  have hen:∀ n,0 ≤ e n := fun n ↦ uniformDistance_nonneg (hb n)
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩:=sourceStripRegularity W γ t ⟨t.property.1.le,t.property.2⟩
  obtain ⟨H,hH,hHb⟩:=hf.deriv.bound_zero
  have hfl:LipschitzWith ⟨H,hH⟩ f := by
    apply lipschitzWith_of_nnnorm_deriv_le (hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne')
    intro x;exact_mod_cast hHb x
  have hbnd (n:ℕ):|(MeasureTheory.integral W.μ (fun z ↦ f (X t z)))-profileResponse (splitTerminal γ t n) f (γ.splitSegment 0 t t.property.1.le n) 0 0| ≤
      H*((∫ s in (0:ℝ)..t,γ.coeff s)-(∫ s in (0:ℝ)..t,profileCoeff (γ.splitSegment 0 t t.property.1.le n) s)+(t:ℝ)*(2*(gridDelta n:ℝ)+γ.coeff t*e n))*Real.exp ((t:ℝ)*γ.coeff t*Lu) := by
    apply (splitTerminal_smooth γ t n).profile_weak_error W.brownian.toIsPreBrownianReal hf
      (γ.splitSegment_mono le_rfl t.property.1 t.property.2.le n)
      (by rw [γ.splitSegment_time,sub_zero]) t.property.1 t.property.2.le hG hLu hu
      (gridDelta n).coe_nonneg (hen n) hH
    · intro s hs
      obtain ⟨r,hr,_,_,he,hrs,_⟩:=γ.splitSegment_sample le_rfl t.property.1 t.property.2.le n
        (show s∈Icc (0:ℝ) ((t:ℝ)-0) by simpa only [sub_zero] using hs)
      rw [he]
      exact add_le_add (γ.monotone hr ⟨hs.1,hs.2.trans_lt t.property.2⟩ (by simpa only [zero_add] using hrs)) le_rfl
    · intro s hs x
      have he:profileValue (splitTerminal γ t n) (γ.splitSegment 0 t t.property.1.le n) s=splitSmooth γ t n s := by
        exact (profileValue_append_before _ _ _ ⟨hs.1,by simpa only [γ.splitSegment_time,sub_zero] using hs.2⟩).symm
      rw [he]
      exact le_uniformDistance (hb n) (⟨s,hs⟩,x)
    · intro x y;exact hfl.dist_le_mul x y
    · intro s hs;exact hX.memLp ⟨hs.1,hs.2.trans t.property.2.le⟩ (by norm_num)
    · exact hX.strip_paths t.property.1.le t.property.2 hLu (fun s hs r hr x y ↦ hu r hr s hs y x)
  have hl:Tendsto (fun n ↦ H*((∫ s in (0:ℝ)..t,γ.coeff s)-(∫ s in (0:ℝ)..t,profileCoeff (γ.splitSegment 0 t t.property.1.le n) s)+(t:ℝ)*(2*(gridDelta n:ℝ)+γ.coeff t*e n))*Real.exp ((t:ℝ)*γ.coeff t*Lu)) atTop (𝓝 0) := by
    have hd:Tendsto (fun n ↦ (gridDelta n:ℝ)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero,add_zero,zero_mul] using
      (((γ.splitPrefix_integral_tendsto t).add (((hd.const_mul 2).add (hel.const_mul (γ.coeff t))).const_mul (t:ℝ))).const_mul H).mul_const (Real.exp ((t:ℝ)*γ.coeff t*Lu))
  rw [←tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (fun n ↦ ?_) hl
  rw [Real.norm_eq_abs,abs_sub_comm]
  exact hbnd n
end SKValue

end

end OAI
