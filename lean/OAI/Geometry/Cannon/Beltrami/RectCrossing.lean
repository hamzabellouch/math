import Mathlib

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonRealPlane

lemma integral_sq_cauchy {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  let aa := ∫ t in a..b, f t
  let bb := ∫ t in a..b, (f t)^2
  let m := aa/(b-a)
  have hfi := hf.intervalIntegrable (μ := volume) a b
  have hf2 : IntervalIntegrable (fun t => (f t)^2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have he : (∫ t in a..b, (f t-m)^2)=bb-2*m*aa+m^2*(b-a) := by
    calc
      _ = ∫ t in a..b, ((f t)^2-2*m*f t+m^2) :=
        intervalIntegral.integral_congr fun _ _ => by ring
      _ = bb-2*m*aa+m^2*(b-a) := by
        rw [intervalIntegral.integral_add (hf2.sub (hfi.const_mul _)) intervalIntegrable_const,
          intervalIntegral.integral_sub hf2 (hfi.const_mul _),intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul,aa,bb]
        ring
  have hp : 0 ≤ ∫ t in a..b, (f t-m)^2 :=
    intervalIntegral.integral_nonneg hab.le (fun _ _ => sq_nonneg _)
  rw [he] at hp
  have ht : 0 < b-a := sub_pos.mpr hab
  have hid : (b-a)*(bb-2*m*aa+m^2*(b-a))=(b-a)*bb-aa^2 := by
    dsimp only [m]
    field_simp
    ring
  have h := mul_nonneg ht.le hp
  rw [hid] at h
  dsimp only [aa,bb] at h
  linarith

lemma line_energy_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {q : ℝ → ℝ}
    (hq : Continuous q) (hp : ∀ x, 0 ≤ q x) (hb : ∀ x, ‖deriv f x‖ ≤ q x)
    {a b x y : ℝ} (hab : a < b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x-f y‖^2 ≤ (b-a)*(∫ t in a..b, (q t)^2) := by
  have hbound (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      ‖f y-f x‖ ≤ ∫ t in a..b, q t := by
    apply (norm_sub_le_integral_of_norm_deriv_le_of_le hxy hf.continuous.continuousOn
      (hf.differentiable (by simp)).differentiableOn (.of_forall (fun t _ => hb t))
      (hq.intervalIntegrable x y)).trans
    exact intervalIntegral.integral_mono_interval hx.1 hxy hy.2 (.of_forall hp)
      (hq.intervalIntegrable a b)
  have h : ‖f x-f y‖ ≤ ∫ t in a..b, q t := by
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev]; exact hbound x y hx hy hxy
    · exact hbound y x hy hx hyx
  have hn : 0 ≤ ∫ t in a..b, q t := intervalIntegral.integral_nonneg hab.le (fun t _ => hp t)
  exact ((sq_le_sq₀ (norm_nonneg _) hn).mpr h).trans (integral_sq_cauchy hq hab)

lemma continuous_line_integral {q : ℝ × ℝ → ℝ} (hq : Continuous q) (a b : ℝ) :
    Continuous (fun x => ∫ y in Icc a b, q (x,y)) :=
  continuous_parametric_integral_of_continuous (f:=fun x y => q (x,y)) hq isCompact_Icc

lemma exists_line_below_average {f : ℝ → ℝ} (hf : Continuous f) {a b E : ℝ}
    (hab : a < b) (hE : (∫ x in Icc a b, f x) ≤ E) :
    ∃ x ∈ Icc a b, f x ≤ E/(b-a) := by
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a,left_mem_Icc.mpr hab.le⟩ hf.continuousOn
  refine ⟨x,hx,(le_div_iff₀ (sub_pos.mpr hab)).mpr ?_⟩
  have hm : (b-a)*f x ≤ ∫ t in Icc a b, f t := by
    calc
      _ = ∫ _t in Icc a b, f x := by simp [Real.volume_real_Icc,hab.le,smul_eq_mul]
      _ ≤ _ := setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top)
        (hf.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc (fun t ht => hmin ht)
  linarith

lemma rectangle_fubini {q : ℝ × ℝ → ℝ} (hq : Continuous q) (a b : ℝ) :
    (∫ p in Icc a b ×ˢ Icc a b, q p) = ∫ x in Icc a b, ∫ y in Icc a b, q (x,y) := by
  have hi : IntegrableOn q (Icc a b ×ˢ Icc a b) volume :=
    hq.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod] at hi ⊢
  exact setIntegral_prod q hi

lemma rectangle_fubini_swap {q : ℝ × ℝ → ℝ} (hq : Continuous q) (a b : ℝ) :
    (∫ p in Icc a b ×ˢ Icc a b, q p) = ∫ y in Icc a b, ∫ x in Icc a b, q (x,y) := by
  rw [rectangle_fubini hq]
  have hi : IntegrableOn q (Icc a b ×ˢ Icc a b) volume :=
    hq.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod] at hi
  change Integrable q ((volume.prod volume).restrict (Icc a b ×ˢ Icc a b)) at hi
  rw [← Measure.prod_restrict (Icc a b) (Icc a b)] at hi
  exact integral_integral_swap hi

lemma vertical_slice_energy {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {a b x y y' : ℝ} (hab : a < b) (hy : y ∈ Icc a b) (hy' : y' ∈ Icc a b) :
    ‖u (x,y)-u (x,y')‖^2 ≤ (b-a)*(∫ t in Icc a b, ‖fderiv ℝ u (x,t)‖^2) := by
  have hf : ContDiff ℝ 1 (fun t : ℝ => u (x,t)) := hu.comp (contDiff_const.prodMk contDiff_id)
  have hq : Continuous (fun t : ℝ => ‖fderiv ℝ u (x,t)‖) :=
    ((hu.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).norm
  have hd (t : ℝ) : ‖deriv (fun s : ℝ => u (x,s)) t‖ ≤ ‖fderiv ℝ u (x,t)‖ := by
    have hs : HasDerivAt (fun s : ℝ => (x,s)) (0,1) t :=
      (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
    have H := (hu.differentiable (by simp) (x,t)).hasFDerivAt.comp_hasDerivAt t hs
    simp only [Function.comp_def] at H
    rw [H.deriv]
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ u (x,t)) (0,1)
  have H := line_energy_bound hf hq (fun t => norm_nonneg _) hd hab hy hy'
  rw [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc] at H
  exact H

lemma horizontal_slice_energy {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {a b x x' y : ℝ} (hab : a < b) (hx : x ∈ Icc a b) (hx' : x' ∈ Icc a b) :
    ‖u (x,y)-u (x',y)‖^2 ≤ (b-a)*(∫ t in Icc a b, ‖fderiv ℝ u (t,y)‖^2) := by
  have hf : ContDiff ℝ 1 (fun t : ℝ => u (t,y)) := hu.comp (contDiff_id.prodMk contDiff_const)
  have hq : Continuous (fun t : ℝ => ‖fderiv ℝ u (t,y)‖) :=
    ((hu.continuous_fderiv (by simp)).comp (continuous_id.prodMk continuous_const)).norm
  have hd (t : ℝ) : ‖deriv (fun s : ℝ => u (s,y)) t‖ ≤ ‖fderiv ℝ u (t,y)‖ := by
    have hs : HasDerivAt (fun s : ℝ => (s,y)) (1,0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    have H := (hu.differentiable (by simp) (t,y)).hasFDerivAt.comp_hasDerivAt t hs
    simp only [Function.comp_def] at H
    rw [H.deriv]
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ u (t,y)) (1,0)
  have H := line_energy_bound hf hq (fun t => norm_nonneg _) hd hab hx hx'
  rw [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc] at H
  exact H

def RectCrossing (u : ℝ × ℝ → ℝ) (c : ℝ) (A B δ : ℝ) : Prop :=
  ∃ a b : ℝ, a ∈ Icc A B ∧ b ∈ Icc A B ∧ δ ≤ b-a ∧
    ((∀ t ∈ Icc a b, ∃ y ∈ Icc A B, u (t,y)=c) ∨
     (∀ t ∈ Icc a b, ∃ x ∈ Icc A B, u (x,t)=c))

lemma norm_sq_triangle (a b c : ℝ) : ‖a-c‖^2 ≤ 2*‖a-b‖^2+2*‖b-c‖^2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub a b c
  have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  nlinarith [sq_nonneg (‖a-b‖-‖b-c‖)]

theorem rectangle_capacity_bound {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {A B δ : ℝ} (hAB : A < B) (hδ : 0 < δ)
    (h0 : RectCrossing u 0 A B δ) (h1 : RectCrossing u 1 A B δ) :
    1 ≤ 8*((B-A)/δ+1)*(∫ p in Icc A B ×ˢ Icc A B, ‖fderiv ℝ u p‖^2) := by
  let q (p : ℝ × ℝ) := ‖fderiv ℝ u p‖^2
  let E := ∫ p in Icc A B ×ˢ Icc A B, q p
  let V (x : ℝ) := ∫ y in Icc A B, q (x,y)
  let H (y : ℝ) := ∫ x in Icc A B, q (x,y)
  have hq : Continuous q := (hu.continuous_fderiv (by simp)).norm.pow 2
  have hV : Continuous V := continuous_line_integral hq A B
  have hH : Continuous H := continuous_line_integral (hq.comp continuous_swap) A B
  have hqp (p : ℝ × ℝ) : 0 ≤ q p := sq_nonneg _
  have hVp (x : ℝ) : 0 ≤ V x := integral_nonneg (fun y => hqp _)
  have hHp (y : ℝ) : 0 ≤ H y := integral_nonneg (fun x => hqp _)
  have hEp : 0 ≤ E := integral_nonneg hqp
  have hEV : (∫ x in Icc A B, V x)=E := (rectangle_fubini hq A B).symm
  have hEH : (∫ y in Icc A B, H y)=E := (rectangle_fubini_swap hq A B).symm
  obtain ⟨x,hx,hxE⟩ := exists_line_below_average hV hAB hEV.le
  obtain ⟨y,hy,hyE⟩ := exists_line_below_average hH hAB hEH.le
  have hcross (c : ℝ) (hc : RectCrossing u c A B δ) :
      ‖u (x,y)-c‖^2 ≤ 2*((B-A)/δ+1)*E := by
    obtain ⟨a,b,ha,hb,hspan,hcross⟩ := hc
    have hab : a < b := by linarith
    have hsub : Icc a b ⊆ Icc A B := Icc_subset_Icc ha.1 hb.2
    rcases hcross with hvertical | hhorizontal
    · have hint : (∫ t in Icc a b, V t) ≤ E := by
        rw [← hEV]
        exact setIntegral_mono_set (hV.continuousOn.integrableOn_compact isCompact_Icc)
          (.of_forall hVp) (.of_forall hsub)
      obtain ⟨t,ht,htE⟩ := exists_line_below_average hV hab hint
      have htE' : V t ≤ E/δ := htE.trans (div_le_div_of_nonneg_left hEp hδ hspan)
      obtain ⟨s,hs,heq⟩ := hvertical t ht
      have hv := vertical_slice_energy hu hAB hy hs (x:=t)
      have hh := horizontal_slice_energy hu hAB hx (hsub ht) (y:=y)
      have htri := norm_sq_triangle (u (x,y)) (u (t,y)) (u (t,s))
      rw [heq] at htri hv
      change ‖u (t,y)-c‖^2 ≤ (B-A)*V t at hv
      change ‖u (x,y)-u (t,y)‖^2 ≤ (B-A)*H y at hh
      have hv' := hv.trans (mul_le_mul_of_nonneg_left htE' (sub_pos.mpr hAB).le)
      have hh' := hh.trans (mul_le_mul_of_nonneg_left hyE (sub_pos.mpr hAB).le)
      rw [mul_div_cancel₀ _ (sub_pos.mpr hAB).ne'] at hh'
      have hid : (B-A)*(E/δ)=((B-A)/δ)*E := by ring
      rw [hid] at hv'
      nlinarith
    · have hint : (∫ t in Icc a b, H t) ≤ E := by
        rw [← hEH]
        exact setIntegral_mono_set (hH.continuousOn.integrableOn_compact isCompact_Icc)
          (.of_forall hHp) (.of_forall hsub)
      obtain ⟨t,ht,htE⟩ := exists_line_below_average hH hab hint
      have htE' : H t ≤ E/δ := htE.trans (div_le_div_of_nonneg_left hEp hδ hspan)
      obtain ⟨s,hs,heq⟩ := hhorizontal t ht
      have hv := vertical_slice_energy hu hAB hy (hsub ht) (x:=x)
      have hh := horizontal_slice_energy hu hAB hx hs (y:=t)
      have htri := norm_sq_triangle (u (x,y)) (u (x,t)) (u (s,t))
      rw [heq] at htri hh
      change ‖u (x,y)-u (x,t)‖^2 ≤ (B-A)*V x at hv
      change ‖u (x,t)-c‖^2 ≤ (B-A)*H t at hh
      have hv' := hv.trans (mul_le_mul_of_nonneg_left hxE (sub_pos.mpr hAB).le)
      have hh' := hh.trans (mul_le_mul_of_nonneg_left htE' (sub_pos.mpr hAB).le)
      rw [mul_div_cancel₀ _ (sub_pos.mpr hAB).ne'] at hv'
      have hid : (B-A)*(E/δ)=((B-A)/δ)*E := by ring
      rw [hid] at hh'
      nlinarith
  have H0 := hcross 0 h0
  have H1 := hcross 1 h1
  have ht := norm_sq_triangle (0:ℝ) (u (x,y)) 1
  simp only [zero_sub,norm_neg,norm_one,one_pow] at ht
  simp only [sub_zero] at H0
  change 1 ≤ 8*((B-A)/δ+1)*E
  nlinarith

lemma preconnected_rectCrossing {u : ℝ × ℝ → ℝ} {c : ℝ}
    {E : Set (ℝ × ℝ)} (hEc : IsPreconnected E) {A B δ : ℝ}
    (hbox : E ⊆ Icc A B ×ˢ Icc A B) (hu : ∀ p ∈ E, u p=c)
    {p q : ℝ × ℝ} (hp : p ∈ E) (hq : q ∈ E) (hd : δ ≤ dist p q) :
    RectCrossing u c A B δ := by
  have hpB := hbox hp
  have hqB := hbox hq
  have hd' : δ ≤ dist p.1 q.1 ∨ δ ≤ dist p.2 q.2 := by
    simpa only [Prod.dist_eq,le_max_iff] using hd
  have hcases (f : ℝ × ℝ → ℝ) (hf : Continuous f) (hfB : ∀ r ∈ E, f r ∈ Icc A B)
      (hh : δ ≤ dist (f p) (f q)) :
      ∃ a b : ℝ, a ∈ Icc A B ∧ b ∈ Icc A B ∧ δ ≤ b-a ∧
        (∀ t ∈ Icc a b, ∃ r ∈ E, f r=t) := by
    rw [Real.dist_eq] at hh
    rcases le_total (f p) (f q) with hle | hle
    · refine ⟨f p,f q,hfB p hp,hfB q hq,?_,?_⟩
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hh
        linarith
      · intro t ht
        exact hEc.intermediate_value hp hq hf.continuousOn ht
    · refine ⟨f q,f p,hfB q hq,hfB p hp,?_,?_⟩
      · simpa only [abs_of_nonneg (sub_nonneg.mpr hle)] using hh
      · intro t ht
        exact hEc.intermediate_value hq hp hf.continuousOn ht
  rcases hd' with hdx | hdy
  · obtain ⟨a,b,ha,hb,hab,hfill⟩ := hcases Prod.fst continuous_fst (fun r hr => (hbox hr).1) hdx
    refine ⟨a,b,ha,hb,hab,Or.inl ?_⟩
    intro t ht
    obtain ⟨r,hr,heq⟩ := hfill t ht
    refine ⟨r.2,(hbox hr).2,?_⟩
    rw [← heq]
    exact hu r hr
  · obtain ⟨a,b,ha,hb,hab,hfill⟩ := hcases Prod.snd continuous_snd (fun r hr => (hbox hr).2) hdy
    refine ⟨a,b,ha,hb,hab,Or.inr ?_⟩
    intro t ht
    obtain ⟨r,hr,heq⟩ := hfill t ht
    refine ⟨r.1,(hbox hr).1,?_⟩
    rw [← heq]
    exact hu r hr

theorem continuum_capacity_bound {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    {E F : Set (ℝ × ℝ)} (hEc : IsPreconnected E) (hFc : IsPreconnected F)
    {A B δ : ℝ} (hAB : A < B) (hδ : 0 < δ)
    (hEB : E ⊆ Icc A B ×ˢ Icc A B) (hFB : F ⊆ Icc A B ×ˢ Icc A B)
    (hE : ∀ p ∈ E, u p=0) (hF : ∀ p ∈ F, u p=1)
    (hdE : ∃ p ∈ E, ∃ q ∈ E, δ ≤ dist p q)
    (hdF : ∃ p ∈ F, ∃ q ∈ F, δ ≤ dist p q) :
    1 ≤ 8*((B-A)/δ+1)*(∫ p in Icc A B ×ˢ Icc A B, ‖fderiv ℝ u p‖^2) := by
  obtain ⟨p,hp,q,hq,hd⟩ := hdE
  obtain ⟨r,hr,s,hs,hd'⟩ := hdF
  exact rectangle_capacity_bound hu hAB hδ
    (preconnected_rectCrossing hEc hEB hE hp hq hd)
    (preconnected_rectCrossing hFc hFB hF hr hs hd')

end CannonRealPlane

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
