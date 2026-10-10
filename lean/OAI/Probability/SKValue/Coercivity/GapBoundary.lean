import Mathlib
import OAI.Probability.SKValue.Variation.OrderVariations

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma OrderParameter.origin_eq_of_constant {γ:OrderParameter} {b c:ℝ} (hb:0<b)
    (he:∀t∈Ioo (0:ℝ) b,γ.coeff t=c):γ.coeff 0=c := by
  have hl:Tendsto γ.coeff (𝓝[>] (0:ℝ)) (𝓝 (γ.coeff 0)) :=
    (γ.rightContinuous 0 ⟨le_rfl,by norm_num⟩).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hr:Tendsto γ.coeff (𝓝[>] (0:ℝ)) (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with t ht htb
    exact (he t ⟨ht,htb⟩).symm
  exact tendsto_nhds_unique hl hr
lemma IsDiffusion.moment_origin {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X):gradientMoment W γ X 0=0 := by
  have hz:∀ᵐ z ∂W.μ,X 0 z=0 := by
    filter_upwards [hX.2,W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with z h h0
    simpa only [Real.toNNReal_zero,intervalIntegral.integral_same,add_zero,h0] using h.2 0 ⟨le_rfl,by norm_num⟩
  unfold gradientMoment
  calc
    (∫ z,(gradient W γ 0 (X 0 z))^2 ∂W.μ)=∫ z,(0:ℝ) ∂W.μ := by
      apply integral_congr_ae
      filter_upwards [hz] with z hz
      rw [hz,phi_gradient_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    _=0:=integral_zero W.Ω ℝ
end SKValue

end

section
open Set
namespace SKValue
lemma positive_gap_endpoints {G:ℝ → ℝ} (hc:ContinuousOn G (Icc (0:ℝ) 1))
    (hn:∀t∈Icc (0:ℝ) 1,0≤G t) (h1:G 1=0) {x:ℝ} (hx:x∈Ioo (0:ℝ) 1) (hxp:0<G x):
    ∃a b:ℝ,0≤a ∧ a<x ∧ x<b ∧ b≤1 ∧ (a=0 ∨ G a=0) ∧ G b=0 ∧
      ∀t∈Ioo a b,0<G t := by
  let K:=Icc (0:ℝ) 1 ∩ G ⁻¹' {0}
  have hK:IsCompact K := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  let L:=(K∩Iic x)∪{0}
  have hL:IsCompact L:=(hK.inter_right isClosed_Iic).union isCompact_singleton
  obtain ⟨a,ha⟩:=hL.exists_isGreatest ⟨0,Or.inr (mem_singleton 0)⟩
  let R:=K∩Ici x
  have hR:IsCompact R:=hK.inter_right isClosed_Ici
  have h1R:1∈R:=⟨⟨⟨by norm_num,le_rfl⟩,h1⟩,hx.2.le⟩
  obtain ⟨b,hb⟩:=hR.exists_isLeast ⟨1,h1R⟩
  have ha0:0≤a:=ha.2 (Or.inr (mem_singleton 0))
  have hax:a<x := by
    rcases ha.1 with ha|ha
    · exact lt_of_le_of_ne ha.2 (fun he ↦ by have hz:=ha.1.2;change G a=0 at hz;rw [he] at hz;linarith)
    · have he:a=0:=ha;simpa only [he] using hx.1
  have hxb:x<b := by
    apply lt_of_le_of_ne hb.1.2
    intro he
    have hz:=hb.1.1.2
    change G b=0 at hz
    rw [←he] at hz
    linarith
  refine ⟨a,b,ha0,hax,hxb,hb.1.1.1.2,?_,hb.1.1.2,?_⟩
  · rcases ha.1 with ha|ha
    · exact Or.inr ha.1.2
    · exact Or.inl ha
  · intro t ht
    have ht01:t∈Icc (0:ℝ) 1:=⟨ha0.trans ht.1.le,ht.2.le.trans hb.1.1.1.2⟩
    apply lt_of_le_of_ne (hn t ht01)
    intro he
    have htK:t∈K:=⟨ht01,he.symm⟩
    by_cases htx:t≤x
    · exact not_le_of_gt ht.1 (ha.2 (Or.inl ⟨htK,htx⟩))
    · exact not_le_of_gt ht.2 (hb.2 ⟨htK,(le_of_not_ge htx)⟩)
end SKValue

end

section
open Set
namespace SKValue

lemma not_three_slope_pattern {f f':ℝ → ℝ} {a x y b:ℝ}
    (hax:a<x) (hxy:x<y) (hyb:y<b) (hc:ContinuousOn f (Icc a b))
    (hd:∀t∈Ioo a b,HasDerivAt f (f' t) t) (hv:ConvexOn ℝ (Ioo a b) f')
    (hleft:f x≤f a) (hmid:f x<f y) (hright:f b≤f y):False := by
  obtain ⟨r,hr,her⟩:=exists_hasDerivAt_eq_slope f f' hax
    (hc.mono (Icc_subset_Icc le_rfl (hxy.le.trans hyb.le)))
    (fun t ht ↦ hd t ⟨ht.1,ht.2.trans hxy |>.trans hyb⟩)
  obtain ⟨s,hs,hes⟩:=exists_hasDerivAt_eq_slope f f' hxy
    (hc.mono (Icc_subset_Icc hax.le hyb.le))
    (fun t ht ↦ hd t ⟨hax.trans ht.1,ht.2.trans hyb⟩)
  obtain ⟨u,hu,heu⟩:=exists_hasDerivAt_eq_slope f f' hyb
    (hc.mono (Icc_subset_Icc (hax.le.trans hxy.le) le_rfl))
    (fun t ht ↦ hd t ⟨hax.trans hxy |>.trans ht.1,ht.2⟩)
  have hr0:f' r≤0:=by rw [her];exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hleft) (sub_pos.mpr hax).le
  have hs0:0<f' s:=by rw [hes];exact div_pos (sub_pos.mpr hmid) (sub_pos.mpr hxy)
  have hu0:f' u≤0:=by rw [heu];exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hright) (sub_pos.mpr hyb).le
  have hh:=hv.le_max_of_mem_Icc ⟨hr.1,hr.2.trans hxy |>.trans hyb⟩
    ⟨hax.trans hxy |>.trans hu.1,hu.2⟩ ⟨(hr.2.trans hs.1).le,(hs.2.trans hu.1).le⟩
  exact (not_lt_of_ge (hh.trans (max_le hr0 hu0))) hs0
end SKValue

end

section
open Set
namespace SKValue
lemma positive_hump_impossible {f f' G:ℝ → ℝ} {a b x:ℝ}
    (hax:a<x) (hxb:x<b) (_:b≤1)
    (hGc:ContinuousOn G (Icc a b)) (hGd:∀t∈Ioo a b,HasDerivAt G (-f t) t)
    (hGa:G a=0) (hGb:G b=0) (hGx:0<G x)
    (hfc:ContinuousOn f (Ico a 1)) (hfd:∀t∈Ioo a b,HasDerivAt f (f' t) t)
    (hfa:f a=0) (hv:ConvexOn ℝ (Ioo a b) f')
    (hend:∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s):False := by
  obtain ⟨r,hr,her⟩:=exists_hasDerivAt_eq_slope G (fun t ↦ -f t) hax
    (hGc.mono (Icc_subset_Icc le_rfl hxb.le)) (fun t ht ↦ hGd t ⟨ht.1,ht.2.trans hxb⟩)
  obtain ⟨s,hs,hes⟩:=exists_hasDerivAt_eq_slope G (fun t ↦ -f t) hxb
    (hGc.mono (Icc_subset_Icc hax.le le_rfl)) (fun t ht ↦ hGd t ⟨hax.trans ht.1,ht.2⟩)
  have hr0:f r<0 := by
    rw [hGa,sub_zero] at her
    have hh:=div_pos hGx (sub_pos.mpr hax)
    linarith
  have hs0:0<f s := by
    rw [hGb,zero_sub] at hes
    have hh:=div_neg_of_neg_of_pos (neg_neg_of_pos hGx) (sub_pos.mpr hxb)
    linarith
  obtain ⟨z,hz,hzb,hfz⟩:=hend s ⟨hax.trans hs.1,hs.2⟩ hs0
  apply not_three_slope_pattern hr.1 (hr.2.trans hs.1) hz.1
    (hfc.mono (fun t ht ↦ ⟨ht.1,ht.2.trans_lt hz.2⟩))
    (fun t ht ↦ hfd t ⟨ht.1,ht.2.trans_le hzb⟩)
    (hv.subset (Ioo_subset_Ioo le_rfl hzb) (convex_Ioo a z))
  · simpa only [hfa] using hr0.le
  · exact hr0.trans hs0
  · exact hfz
lemma endpoint_condition {f:ℝ → ℝ} {a b:ℝ} (hb:b≤1)
    (hfb:b<1 → f b=0) (hbound:∀t∈Ioo a 1,f t≤1-t):
    ∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s := by
  intro s hs hfs
  rcases hb.lt_or_eq with hb|rfl
  · exact ⟨b,⟨hs.2,hb⟩,le_rfl,by rw [hfb hb];exact hfs.le⟩
  · have hm:max s (1-f s)<1:=max_lt hs.2 (by linarith)
    obtain ⟨z,hz,hz1⟩:=exists_between hm
    refine ⟨z,⟨(le_max_left _ _).trans_lt hz,hz1⟩,hz1.le,?_⟩
    have hsz:s<z:=(le_max_left _ _).trans_lt hz
    have hgz:1-f s<z:=(le_max_right _ _).trans_lt hz
    have hh:=hbound z ⟨hs.1.trans hsz,hz1⟩
    linarith
end SKValue

end

end OAI
