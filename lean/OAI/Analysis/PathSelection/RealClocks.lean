import Mathlib
import OAI.Analysis.PathSelection.ClockInverses

namespace OAI

/-! Real leading terms, conjugation and logarithmic derivative bounds. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma SectorExpansion.top_nonnegative {F : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hF : SectorExpansion F E b) {β : ℝ} (hmax : ∀ γ∈E,γ≤β)
    (hlim : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop) : 0≤β := by
  by_contra hn
  have hβ : β<0 := lt_of_not_ge hn
  have hh := hF.negative_bound (δ := -β) (by linarith)
    (fun γ hγ => by simpa using hmax γ hγ)
  have ht := hh.tendsto_zero (by linarith : -(-β)/2<0)
  have hz := (Complex.continuous_re.tendsto 0).comp (ht.comp tendsto_real_sectorInfinity)
  exact not_tendsto_nhds_of_tendsto_atTop hlim 0 hz

 

theorem ExpansionOver.puiseux_unbounded_leading {F : ℂ → ℂ}
    (hF : ExpansionOver PuiseuxSector F)
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hlim : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop) :
    ∃ β : ℝ,0≤β ∧ ∃ b : ℂ → ℂ,b∈PuiseuxSector ∧
      (¬ (fun t : ℝ => b (t:ℂ)) =ᶠ[atTop] fun _ => 0) ∧
      ExpSmall 0 (fun z => Complex.exp (((-β:ℝ):ℂ)*z)*(b z)⁻¹*F z-1) ∧
      Tendsto (fun z => deriv F z/F z) sectorInfinity (𝓝 (β:ℂ)) ∧
      (0<β → ∃ A T : ℝ,0<T ∧ ∃ x : ℂ → ℂ,
        AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
        (∀ w : ℂ,0<w.re → T<‖w‖ → F (x w)=w) ∧
        (∀ w : ℂ,0<w.re → T<‖w‖ → ∃ t : ℝ,A<t ∧
          F (t:ℂ)=(‖w‖:ℂ) ∧ ‖x w-(t:ℂ)‖≤2*|w.arg|/β) ∧
        (∀ᶠ t : ℝ in atTop,x (F (t:ℂ))=(t:ℂ))) := by
  obtain ⟨E,b,hF,hb⟩ := hF
  have ht := hF.trim_zero (fun β hβ => (hb β hβ).1)
  have hn : (nonzeroRaySupport E b).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he] at ht
    have hz := ht.empty
    have hfalse : ∀ᶠ t : ℝ in atTop,False := by
      filter_upwards [hr,hz] with t hr hz
      simpa [hz] using hr.2
    obtain ⟨t,ht⟩ := hfalse.exists
    exact ht
  obtain ⟨β,hβ,hmax⟩ := exists_greatest_of_finite_above ht.finite_above hn
  have hbi := puiseux_lowerSectorData.slow (puiseux_lowerSectorData.inv_mem (hb β hβ.1))
  have hb0 : ∀ᶠ z in sectorInfinity,b β z≠0 := by
    rcases puiseux_lowerSectorData.zero_or_ne (hb β hβ.1) with hz | hz
    · exact False.elim (hβ.2 (tendsto_real_sectorInfinity.eventually hz))
    · exact hz
  have hq := ht.log_deriv_tendsto (fun γ hγ => (hb γ hγ.1).1) hβ hmax hb0 hbi
    (PuiseuxSector.log_deriv_tendsto (hb β hβ.1) hβ.2)
  refine ⟨β,ht.top_nonnegative hmax hlim,b β,hb β hβ.1,hβ.2,
    ht.uniform_leading hβ hmax hb0 hbi,hq,?_⟩
  intro hpos
  exact positive_exponential_inverse hpos
    (Filter.Eventually.filter_mono stripInfinity_le_sectorInfinity ht.eventually_analytic)
    (Filter.Eventually.filter_mono stripInfinity_le_sectorInfinity (ht.eventually_ne_of_leading hβ hmax hb0 hbi))
    hr hlim (hq.mono_left stripInfinity_le_sectorInfinity)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma analyticAt_reflection {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F (star z)) :
    AnalyticAt ℂ (fun w => star (F (star w))) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hc : Tendsto (star : ℂ → ℂ) (𝓝 z) (𝓝 (star z)) := continuous_star.continuousAt.tendsto
  filter_upwards [hc.eventually hF.eventually_analyticAt] with w hw
  simpa only [Function.comp_def, Complex.star_def, Complex.conj_conj] using hw.differentiableAt.conj_conj

lemma mem_lossSector_star {ω : ℝ → ℝ} {R : ℝ} {z : ℂ}
    (hz : z ∈ lossSector ω R) : star z ∈ lossSector ω R := by
  have harg : |(star z).arg|=|z.arg| := by
    rw [Complex.star_def,Complex.arg_conj]
    split_ifs with h
    · rw [h]
    · exact abs_neg _
  simpa only [lossSector,mem_ofPred_eq,norm_star,harg] using hz

lemma SectorExpansion.conj {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b) :
    SectorExpansion (fun z => star (f (star z))) E (fun β z => star (b β (star z))) := by
  classical
  refine ⟨h.bounded_above,h.finite_above,?_⟩
  intro B
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hb⟩ := h.remainders B
  refine ⟨ω,R,ε,C,hω,hε,hC,fun z hz => analyticAt_reflection (hf _ (mem_lossSector_star hz)),?_⟩
  intro z hz
  have hbound := hb (star z) (mem_lossSector_star hz)
  rw [←norm_star] at hbound
  simpa only [star_sub,star_sum,star_mul,Complex.star_def,←Complex.exp_conj,
    map_mul,Complex.conj_ofReal,Complex.conj_conj,Complex.conj_re,mul_comm] using hbound

lemma ClockGerm.conj {xs : List (ℝ → ℝ)} {f : ℝ → ℂ} (hf : ClockGerm xs f) :
    ClockGerm xs (fun t => star (f t)) := by
  induction xs generalizing f with
  | nil => exact Puiseux.conj hf
  | cons X xs ih =>
    obtain ⟨F,E,b,hF,hb,he⟩ := hf
    refine ⟨fun z => star (F (star z)),E,fun β z => star (b β (star z)),hF.conj,?_,?_⟩
    · intro β hβ
      constructor
      · simpa only [Complex.star_def,Complex.conj_ofReal] using ih (hb β hβ).1
      · obtain ⟨ω,R,hω,ha⟩ := (hb β hβ).2
        exact ⟨ω,R,hω,fun z hz => analyticAt_reflection (ha _ (mem_lossSector_star hz))⟩
    · filter_upwards [he] with t ht
      simp only [ht,Complex.star_def,Complex.conj_ofReal]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma SectorExpansion.congr_coeff {F : ℂ → ℂ} {E : Set ℝ} {b c : ℝ → ℂ → ℂ}
    (h : SectorExpansion F E b) (he : ∀ β∈E,b β=c β) : SectorExpansion F E c := by
  refine ⟨h.bounded_above,h.finite_above,?_⟩
  intro B
  obtain ⟨ω,R,ε,C,hω,hε,hC,ha,hb⟩ := h.remainders B
  refine ⟨ω,R,ε,C,hω,hε,hC,ha,?_⟩
  intro z hz
  convert hb z hz using 1
  congr 2
  apply Finset.sum_congr rfl
  intro β hβ
  rw [he β ((h.finite_above B).mem_toFinset.mp hβ).1]

lemma SectorExpansion.add_same {F G : ℂ → ℂ} {E : Set ℝ} {b c : ℝ → ℂ → ℂ}
    (hF : SectorExpansion F E b) (hG : SectorExpansion G E c) :
    SectorExpansion (fun z => F z+G z) E (fun β z => b β z+c β z) := by
  classical
  have hh := hF.add hG
  rw [union_self] at hh
  apply hh.congr_coeff
  intro β hβ
  simp only [ite_eq_left hβ]

lemma PuiseuxSector.reflect {F : ℂ → ℂ} (hF : F∈PuiseuxSector) :
    (fun z => star (F (star z)))∈PuiseuxSector := by
  refine ⟨?_,?_⟩
  · obtain ⟨ω,R,hω,ha⟩ := hF.1
    exact ⟨ω,R,hω,fun z hz => analyticAt_reflection (ha _ (mem_lossSector_star hz))⟩
  · simpa only [Complex.star_def,Complex.conj_ofReal] using hF.2.conj

lemma ExpansionOver.puiseux_real_expansion {F : ℂ → ℂ} (hF : ExpansionOver PuiseuxSector F)
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0) :
    ∃ E : Set ℝ,∃ b : ℝ → ℂ → ℂ,SectorExpansion F E b ∧
      (∀ β∈E,b β∈PuiseuxSector) ∧ (∀ β t : ℝ,(b β (t:ℂ)).im=0) := by
  obtain ⟨E,b,hF,hb⟩ := hF
  let c : ℂ := 1/2
  have hc := puiseux_lowerSectorData.const_mem c
  have hs := (hF.add_same hF.conj).mul_lower hc.1 (puiseux_lowerSectorData.slow hc)
  have he : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)+star (F (star (t:ℂ))))*c=F (t:ℂ) := by
    filter_upwards [hr] with t ht
    have heq : F (t:ℂ)=((F (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using ht)
    simp only [Complex.star_def,Complex.conj_ofReal]
    rw [heq,Complex.conj_ofReal]
    dsimp [c]
    ring
  have he' := sector_analytic_eq_of_ray hs.eventually_analytic hF.eventually_analytic he
  refine ⟨E,fun β z => (b β z+star (b β (star z)))*c,hs.congr he',?_,?_⟩
  · intro β hβ
    exact puiseux_lowerSectorData.mul_mem
      (puiseux_lowerSectorData.add_mem (hb β hβ) (PuiseuxSector.reflect (hb β hβ))) hc
  · intro β t
    simp [c,Complex.mul_im]

lemma positive_real_factor_of_normalized {F b : ℂ → ℂ} {β : ℝ}
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hbr : ∀ᶠ t : ℝ in atTop,(b (t:ℂ)).im=0)
    (ht : Tendsto (fun t : ℝ => Complex.exp (((-β:ℝ):ℂ)*(t:ℂ))*(b (t:ℂ))⁻¹*F (t:ℂ)) atTop (𝓝 1)) :
    ∀ᶠ t : ℝ in atTop,0<(b (t:ℂ)).re := by
  have hr := (Complex.continuous_re.tendsto 1).comp ht
  simp only [Complex.one_re] at hr
  filter_upwards [hr.eventually (eventually_gt_nhds zero_lt_one),hFr,hbr] with t hp hf hb
  have hF : F (t:ℂ)=((F (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hf.1)
  have hB : b (t:ℂ)=((b (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hb)
  dsimp only [Function.comp_apply] at hp
  rw [hF,hB,←Complex.ofReal_mul,←Complex.ofReal_exp,←Complex.ofReal_inv,←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.ofReal_re] at hp
  have hinv : 0<((b (t:ℂ)).re)⁻¹ := by
    have hm := (mul_pos_iff_of_pos_right hf.2).mp hp
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hm
  exact inv_pos.mp hinv

 

theorem ExpansionOver.puiseux_positive_leading {F : ℂ → ℂ}
    (hF : ExpansionOver PuiseuxSector F)
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hlim : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop) :
    ∃ β : ℝ,0≤β ∧ ∃ b : ℂ → ℂ,b∈PuiseuxSector ∧
      (∀ᶠ z in sectorInfinity,b z≠0) ∧
      (∀ᶠ t : ℝ in atTop,(b (t:ℂ)).im=0 ∧ 0<(b (t:ℂ)).re) ∧
      ExpSmall 0 (fun z => Complex.exp (((-β:ℝ):ℂ)*z)*(b z)⁻¹*F z-1) ∧
      Tendsto (fun z => deriv F z/F z) sectorInfinity (𝓝 (β:ℂ)) := by
  obtain ⟨E,b,hF,hb,hbr⟩ := hF.puiseux_real_expansion (hr.mono fun _ h => h.1)
  have ht := hF.trim_zero (fun β hβ => (hb β hβ).1)
  have hn : (nonzeroRaySupport E b).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he] at ht
    have hz := ht.empty
    obtain ⟨t,hr,hz⟩ := (hr.and hz).exists
    have hh : 0<(F (t:ℂ)).re := hr.2
    change F (t:ℂ)=0 at hz
    rw [hz,Complex.zero_re] at hh
    exact lt_irrefl _ hh
  obtain ⟨β,hβ,hmax⟩ := exists_greatest_of_finite_above ht.finite_above hn
  have hbi := puiseux_lowerSectorData.slow (puiseux_lowerSectorData.inv_mem (hb β hβ.1))
  have hb0 : ∀ᶠ z in sectorInfinity,b β z≠0 := by
    rcases puiseux_lowerSectorData.zero_or_ne (hb β hβ.1) with hz | hz
    · exact False.elim (hβ.2 (tendsto_real_sectorInfinity.eventually hz))
    · exact hz
  have hu := ht.uniform_leading hβ hmax hb0 hbi
  have hbt := positive_real_factor_of_normalized hr (Eventually.of_forall (hbr β))
    ((ht.uniform_leading_tendsto hβ hmax hb0 hbi).comp tendsto_real_sectorInfinity)
  exact ⟨β,ht.top_nonnegative hmax hlim,b β,hb β hβ.1,hb0,
    (Eventually.of_forall (hbr β)).and hbt,hu,
    ht.log_deriv_tendsto (fun γ hγ => (hb γ hγ.1).1) hβ hmax hb0 hbi
      (PuiseuxSector.log_deriv_tendsto (hb β hβ.1) hβ.2)⟩

end DegeneratingTrees.Clock

 

 

 

open Set Complex Metric
namespace DegeneratingTrees.Clock

lemma log_deriv_bound_of_log_norm_bound {F : ℂ → ℂ} {z : ℂ} {R M : ℝ}
    (hR : 0<R) (hM : 0<M) (hF : AnalyticOnNhd ℂ F (ball z R))
    (hF0 : ∀ w∈ball z R,F w≠0)
    (hbound : ∀ w∈ball z R,|Real.log ‖F w‖|≤M) :
    ‖deriv F z/F z‖≤8*M/R := by
  obtain ⟨L,hLa,hLe,hLd⟩ := analytic_log_on_convex isOpen_ball (convex_ball z R)
    ⟨z,mem_ball_self hR⟩ hF hF0
  have hLre (w : ℂ) (hw : w∈ball z R) : |(L w).re|≤M := by
    have hn := congrArg norm (hLe w hw)
    rw [Complex.norm_exp] at hn
    have hlog := congrArg Real.log hn
    rw [Real.log_exp] at hlog
    rw [hlog]
    exact hbound w hw
  let K : ℂ → ℂ := fun v => L (z+v)-L z
  have hmem {v : ℂ} (hv : v∈ball 0 R) : z+v∈ball z R := by
    simpa only [mem_ball_iff_norm,add_sub_cancel_left,sub_zero] using hv
  have hKa : AnalyticOnNhd ℂ K (ball 0 R) := by
    intro v hv
    exact ((hLa _ (hmem hv)).comp (analyticAt_const.add analyticAt_id)).sub analyticAt_const
  have hKre : MapsTo K (ball 0 R) {v | v.re≤2*M} := by
    intro v hv
    change (L (z+v)).re-(L z).re≤2*M
    have h1 := abs_le.mp (hLre _ (hmem hv))
    have h0 := abs_le.mp (hLre _ (mem_ball_self hR))
    linarith
  have hKb (v : ℂ) (hv : v∈sphere 0 (R/2)) : ‖K v‖≤4*M := by
    have hn : ‖v‖=R/2 := by simpa only [mem_sphere_iff_norm,sub_zero] using hv
    have hvR : v∈ball 0 R := by rw [mem_ball_zero_iff,hn]; linarith
    have hh := Complex.borelCaratheodory_zero (f := K) (by positivity : 0<2*M)
      hKa.differentiableOn hKre hR hvR (by simp [K])
    rw [hn] at hh
    convert hh using 1
    field_simp
    ring
  have hs : closure (ball (0:ℂ) (R/2)) ⊆ ball 0 R := by
    rw [closure_ball _ (by positivity : R/2≠0)]
    intro v hv
    rw [mem_ball_zero_iff]
    have hn : ‖v‖≤R/2 := by simpa only [mem_closedBall_iff_norm,sub_zero] using hv
    linarith
  have hc : DiffContOnCl ℂ K (ball 0 (R/2)) :=
    ((hKa.mono hs).differentiableOn).diffContOnCl
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0<R/2) hc hKb
  have hKd : deriv K 0=deriv L z := by
    have hLz : HasDerivAt L (deriv L z) (z+id (0:ℂ)) := by
      simpa using (hLa z (mem_ball_self hR)).differentiableAt.hasDerivAt
    have hh := (hLz.comp 0
      ((hasDerivAt_id (0:ℂ)).const_add z)).sub_const (L z)
    simpa only [K,Function.comp_def,id_eq,mul_one] using hh.deriv
  rw [hKd,hLd _ (mem_ball_self hR)] at hd
  convert hd using 1
  field_simp
  ring

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
namespace DegeneratingTrees.Clock

lemma SectorSlow.log_deriv_tendsto {F : ℂ → ℂ}
    (hFa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z)
    (hF0 : ∀ᶠ z in sectorInfinity,F z≠0)
    (hf : SectorSlow F) (hi : SectorSlow (fun z => (F z)⁻¹)) :
    Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/512
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hCb⟩ := (hf δ hδ).exists_pos
  obtain ⟨D,hD,hDb⟩ := (hi δ hδ).exists_pos
  have hbound : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z ∧ F z≠0 ∧
      |Real.log ‖F z‖|≤|Real.log C|+|Real.log D|+δ*z.re := by
    filter_upwards [hFa,hF0,hCb.bound,hDb.bound] with z ha hz hc hd
    simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_inv] at hc hd
    have hn : 0<‖F z‖ := norm_pos_iff.mpr hz
    have hu := Real.log_le_log hn hc
    have hl := Real.log_le_log (inv_pos.mpr hn) hd
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _),Real.log_exp] at hu
    rw [Real.log_mul hD.ne' (Real.exp_ne_zero _),Real.log_exp,Real.log_inv] at hl
    refine ⟨ha,hz,abs_le.mpr ⟨?_,?_⟩⟩
    · linarith [le_abs_self (Real.log D),abs_nonneg (Real.log C)]
    · linarith [le_abs_self (Real.log C),abs_nonneg (Real.log D)]
  obtain ⟨ω,S,hω,hS⟩ := hbound
  intro W
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hω.real_discs S)
  let K := |Real.log C|+|Real.log D|+1
  have hK : 0<K := by dsimp [K]; positivity
  let A := max T (max (8*|W|+1) (256*K/ε))
  refine ⟨A,?_⟩
  intro z hz
  have hzt : T<z.re := (le_max_left _ _).trans_lt hz.1
  have hzw : 8*|W|+1<z.re :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hz.1
  have hze : 256*K/ε<z.re :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hz.1
  have hzp : 0<z.re := by linarith [abs_nonneg W]
  have hzi : |z.im|<z.re/8 := by linarith [hz.2,le_abs_self W]
  have hdisc : ball z (z.re/8) ⊆ lossSector ω S := by
    intro v hv
    apply (hT z.re hzt.le).2
    rw [mem_closedBall_iff_norm]
    have hn : ‖z-(z.re:ℂ)‖=|z.im| := by
      have he : z-(z.re:ℂ)=Complex.I*(z.im:ℂ) := by apply Complex.ext <;> simp
      rw [he,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
    have hvn : ‖v-z‖<z.re/8 := mem_ball_iff_norm.mp hv
    calc
      ‖v-(z.re:ℂ)‖ = ‖(v-z)+(z-(z.re:ℂ))‖ := by congr 1; ring
      _ ≤ ‖v-z‖+‖z-(z.re:ℂ)‖ := norm_add_le _ _
      _ ≤ z.re/4 := by rw [hn]; linarith
  have hlog (v : ℂ) (hv : v∈ball z (z.re/8)) :
      |Real.log ‖F v‖|≤K+2*δ*z.re := by
    have hre := (le_abs_self (v-z).re).trans (Complex.abs_re_le_norm (v-z))
    simp only [Complex.sub_re] at hre
    have hn : ‖v-z‖<z.re/8 := mem_ball_iff_norm.mp hv
    have hvr : v.re≤2*z.re := by linarith
    have hh := (hS v (hdisc hv)).2.2
    have hm := mul_le_mul_of_nonneg_left hvr hδ.le
    dsimp [K]
    linarith
  have hd := log_deriv_bound_of_log_norm_bound (F := F) (z := z)
    (by positivity : 0<z.re/8) (by positivity : 0<K+2*δ*z.re)
    (fun v hv => (hS v (hdisc hv)).1) (fun v hv => (hS v (hdisc hv)).2.1) hlog
  change dist (deriv F z/F z) 0<ε
  rw [dist_zero_right]
  apply hd.trans_lt
  rw [div_lt_iff₀ (by positivity : 0<z.re/8)]
  have he := (div_lt_iff₀ hε).mp hze
  dsimp [δ]
  nlinarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma LowerSectorData.log_deriv_strip {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    {F : ℂ → ℂ} (hF : F∈K) (hn : ∀ᶠ z in sectorInfinity,F z≠0) :
    Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 0) :=
  SectorSlow.log_deriv_tendsto (hK.analytic hF) hn (hK.slow hF) (hK.slow (hK.inv_mem hF))

lemma SectorExpansion.log_deriv_strip {F : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hF : SectorExpansion F E b) (ha : ∀ β∈E,∀ᶠ z in sectorInfinity,AnalyticAt ℂ (b β) z)
    {β : ℝ} (hβ : β∈E) (hmax : ∀ γ∈E,γ≤β)
    (hb0 : ∀ᶠ z in sectorInfinity,b β z≠0) (hbi : SectorSlow (fun z => (b β z)⁻¹))
    (hq : Tendsto (fun z => _root_.deriv (b β) z/b β z) stripInfinity (𝓝 0)) :
    Tendsto (fun z => _root_.deriv F z/F z) stripInfinity (𝓝 (β:ℂ)) := by
  have hFd := hF.deriv ha
  have herr := ((hFd.leading_error hβ hmax).mul (ExpBound.cexp (-β))).mul_slow hbi
  simp only [add_neg_cancel] at herr
  have hn : Tendsto (fun z => Complex.exp (((-β:ℝ):ℂ)*z)*(b β z)⁻¹*_root_.deriv F z)
      stripInfinity (𝓝 (β:ℂ)) := by
    have ht := (herr.tendsto_zero.mono_left stripInfinity_le_sectorInfinity).add ((tendsto_const_nhds (x := (β:ℂ))).add hq)
    simp only [add_zero,zero_add] at ht
    apply ht.congr'
    filter_upwards [hb0.filter_mono stripInfinity_le_sectorInfinity] with z hz
    have he : Complex.exp (((-β:ℝ):ℂ)*z)=(Complex.exp ((β:ℂ)*z))⁻¹ := by
      rw [←Complex.exp_neg]; congr 1; push_cast; ring
    rw [he]
    field_simp [hz,Complex.exp_ne_zero]
    ring
  have hu := (hF.uniform_leading_tendsto hβ hmax hb0 hbi).mono_left stripInfinity_le_sectorInfinity
  have ht := hn.div hu (by norm_num : (1:ℂ)≠0)
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [hb0.filter_mono stripInfinity_le_sectorInfinity,
    (hF.eventually_ne_of_leading hβ hmax hb0 hbi).filter_mono stripInfinity_le_sectorInfinity] with z hz hFz
  change (Complex.exp (((-β:ℝ):ℂ)*z)*(b β z)⁻¹*_root_.deriv F z) /
    (Complex.exp (((-β:ℝ):ℂ)*z)*(b β z)⁻¹*F z)=_root_.deriv F z/F z
  field_simp [hz,hFz,Complex.exp_ne_zero]

lemma ExpansionOver.real_expansion {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K) {F : ℂ → ℂ} (hF : ExpansionOver K F)
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0) :
    ∃ E : Set ℝ,∃ b : ℝ → ℂ → ℂ,SectorExpansion F E b ∧
      (∀ β∈E,b β∈K) ∧ (∀ β t : ℝ,(b β (t:ℂ)).im=0) := by
  obtain ⟨E,b,hF,hb⟩ := hF
  let c : ℂ := 1/2
  have hc := hK.const_mem c
  have hs := (hF.add_same hF.conj).mul_lower (hK.analytic hc) (hK.slow hc)
  have he : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)+star (F (star (t:ℂ))))*c=F (t:ℂ) := by
    filter_upwards [hr] with t ht
    have heq : F (t:ℂ)=((F (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using ht)
    simp only [Complex.star_def,Complex.conj_ofReal]
    rw [heq,Complex.conj_ofReal]
    dsimp [c]
    ring
  have he' := sector_analytic_eq_of_ray hs.eventually_analytic hF.eventually_analytic he
  refine ⟨E,fun β z => (b β z+star (b β (star z)))*c,hs.congr he',?_,?_⟩
  · intro β hβ
    exact hK.mul_mem
      (hK.add_mem (hb β hβ) (hconj _ (hb β hβ))) hc
  · intro β t
    simp [c,Complex.mul_im]

theorem ExpansionOver.positive_leading_strip {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K) {F : ℂ → ℂ}
    (hF : ExpansionOver K F)
    (hr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hlim : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop) :
    ∃ β : ℝ,0≤β ∧ ∃ b : ℂ → ℂ,b∈K ∧
      (∀ᶠ z in sectorInfinity,b z≠0) ∧
      (∀ᶠ t : ℝ in atTop,(b (t:ℂ)).im=0 ∧ 0<(b (t:ℂ)).re) ∧
      ExpSmall 0 (fun z => Complex.exp (((-β:ℝ):ℂ)*z)*(b z)⁻¹*F z-1) ∧
      Tendsto (fun z => deriv F z/F z) stripInfinity (𝓝 (β:ℂ)) := by
  obtain ⟨E,b,hF,hb,hbr⟩ := hF.real_expansion hK hconj (hr.mono fun _ h => h.1)
  have ht := hF.trim_zero (fun β hβ => hK.analytic (hb β hβ))
  have hn : (nonzeroRaySupport E b).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he] at ht
    have hz := ht.empty
    obtain ⟨t,hr,hz⟩ := (hr.and hz).exists
    have hh : 0<(F (t:ℂ)).re := hr.2
    change F (t:ℂ)=0 at hz
    rw [hz,Complex.zero_re] at hh
    exact lt_irrefl _ hh
  obtain ⟨β,hβ,hmax⟩ := exists_greatest_of_finite_above ht.finite_above hn
  have hbi := hK.slow (hK.inv_mem (hb β hβ.1))
  have hb0 : ∀ᶠ z in sectorInfinity,b β z≠0 := by
    rcases hK.zero_or_ne (hb β hβ.1) with hz | hz
    · exact False.elim (hβ.2 (tendsto_real_sectorInfinity.eventually hz))
    · exact hz
  have hu := ht.uniform_leading hβ hmax hb0 hbi
  have hbt := positive_real_factor_of_normalized hr (Eventually.of_forall (hbr β))
    ((ht.uniform_leading_tendsto hβ hmax hb0 hbi).comp tendsto_real_sectorInfinity)
  exact ⟨β,ht.top_nonnegative hmax hlim,b β,hb β hβ.1,hb0,
    (Eventually.of_forall (hbr β)).and hbt,hu,
    ht.log_deriv_strip (fun γ hγ => hK.analytic (hb γ hγ.1)) hβ hmax hb0 hbi
      (hK.log_deriv_strip (hb β hβ.1) hb0)⟩

end DegeneratingTrees.Clock
end

end OAI
