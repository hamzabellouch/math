import Mathlib
import OAI.Analysis.PathSelection.EqualExponentCharts
import OAI.Analysis.PathSelection.LowerRatios

namespace OAI

/-! Positive clock charts, power sectors and changes of Puiseux clock. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

def PositiveExponentialChart (F H : ℂ → ℂ) : Prop :=
  ∃ (T : ℝ) (x : ℂ → ℂ),0<T ∧
    AnalyticOnNhd ℂ x {w | 0<w.re ∧ T<‖w‖} ∧
    (∀ w : ℂ,0<w.re → T<‖w‖ → H (x w)=w) ∧
    (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
    Tendsto x sectorInfinity stripInfinity ∧
    (∀ᶠ r : ℝ in atTop,(x (r:ℂ)).im=0 ∧ (F (x (r:ℂ))).im=0 ∧ 0<(F (x (r:ℂ))).re) ∧
    Tendsto (fun r : ℝ => (F (x (r:ℂ))).re) atTop atTop ∧
    (∀ᶠ w in sectorInfinity,AnalyticAt ℂ (fun z => F (x z)) w) ∧
    ∀ (ω : ℝ → ℝ) (S : ℝ),AdmissibleAngularLoss ω →
      ∃ (η : ℝ → ℝ) (R : ℝ),AdmissibleAngularLoss η ∧
        (∀ w∈lossSector η R,F (x w)∈lossSector ω S) ∧
        (∀ w∈lossSector η R,(F (x (‖w‖:ℂ))).re/2≤‖F (x w)‖ ∧
          ‖F (x w)‖≤2*(F (x (‖w‖:ℂ))).re) ∧
        (Tendsto (fun t : ℝ => F (t:ℂ)/H (t:ℂ)) atTop (𝓝 0) →
          ∀ ε : ℝ,0<ε → ∃ U : ℝ,∀ w∈lossSector η U,|(F (x w)).re|≤ε*w.re)

lemma normalized_leading_nonzero {F g : ℂ → ℂ} {a : ℝ}
    (he : ExpSmall 0 (fun z => Complex.exp (((-a:ℝ):ℂ)*z)*(g z)⁻¹*F z-1)) :
    ∀ᶠ z in sectorInfinity,F z≠0 := by
  have ht : Tendsto (fun z => Complex.exp (((-a:ℝ):ℂ)*z)*(g z)⁻¹*F z) sectorInfinity (𝓝 1) := by
    simpa only [sub_add_cancel,zero_add] using he.tendsto_zero.add_const 1
  filter_upwards [ht.eventually_ne (by norm_num : (1:ℂ)≠0)] with z hz
  intro heq
  simp [heq] at hz

lemma ExpSmall.strip_bound {E : ℂ → ℂ} (he : ExpSmall 0 E) :
    ∃ ε C : ℝ,0<ε ∧ 0≤C ∧ ∀ᶠ z in stripInfinity,‖E z‖≤C*Real.exp (-ε*z.re) := by
  obtain ⟨a,ha,hO⟩ := he
  obtain ⟨C,hC,hbound⟩ := hO.exists_pos
  refine ⟨-a,C,by linarith,hC.le,?_⟩
  simpa only [neg_neg,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    hbound.bound.filter_mono stripInfinity_le_sectorInfinity

lemma real_positive_quotient {g h : ℂ → ℂ}
    (hg : ∀ᶠ t : ℝ in atTop,(g (t:ℂ)).im=0 ∧ 0<(g (t:ℂ)).re)
    (hh : ∀ᶠ t : ℝ in atTop,(h (t:ℂ)).im=0 ∧ 0<(h (t:ℂ)).re) :
    ∀ᶠ t : ℝ in atTop,(g (t:ℂ)/h (t:ℂ)).im=0 ∧ 0<(g (t:ℂ)/h (t:ℂ)).re := by
  filter_upwards [hg,hh] with t hg hh
  have eg : g (t:ℂ)=((g (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hg.1)
  have eh : h (t:ℂ)=((h (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hh.1)
  rw [eg,eh,←Complex.ofReal_div]
  exact ⟨rfl,div_pos hg.2 hh.2⟩

 

theorem ExpansionOver.first_positive_chart {F H : ℂ → ℂ}
    (hF : ExpansionOver PuiseuxSector F) (hH : ExpansionOver PuiseuxSector H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re)
    (htop : ∃ b : ℝ,0<b ∧ Tendsto (fun z => deriv H z/H z) sectorInfinity (𝓝 (b:ℂ))) :
    PositiveExponentialChart F H := by
  obtain ⟨a,ha,g,hg,hg0,hgr,hFe,hFd⟩ := hF.puiseux_positive_leading hFr hFt
  obtain ⟨b,hb,h,hh,hh0,hhr,hHe,hHd⟩ := hH.puiseux_positive_leading hHr hHt
  obtain ⟨b',hb',hHd'⟩ := htop
  have heq : b=b' := Complex.ofReal_injective (tendsto_nhds_unique hHd hHd')
  have hbpos : 0<b := heq.symm ▸ hb'
  obtain ⟨_,_,hFs,_⟩ := hF
  obtain ⟨_,_,hHs,_⟩ := hH
  have hFa := hFs.eventually_analytic
  have hHa := hHs.eventually_analytic
  have hF0 := normalized_leading_nonzero hFe
  have hH0 := normalized_leading_nonzero hHe
  have hab : a≤b := unbounded_log_exponent_order hb
    (tendsto_real_sectorInfinity.eventually hFa) (tendsto_real_sectorInfinity.eventually hHa)
    hFr hHr hFt (hFd.comp tendsto_real_sectorInfinity) (hHd.comp tendsto_real_sectorInfinity) hO
  have hs {P : ℂ → Prop} (hp : ∀ᶠ z in sectorInfinity,P z) : ∀ᶠ z in stripInfinity,P z :=
    hp.filter_mono stripInfinity_le_sectorInfinity
  have hdfs := hFd.mono_left stripInfinity_le_sectorInfinity
  have hdhs := hHd.mono_left stripInfinity_le_sectorInfinity
  rcases hab.lt_or_eq with hab | hab
  · obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := strict_exponential_chart ha hab
      (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs
    refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
    intro ω S hω
    obtain ⟨η,R,hη,hm,hn,he⟩ := hmap ω S hω
    exact ⟨η,R,hη,hm,hn,fun _ => he⟩
  · subst a
    let J : ℂ → ℂ := fun z => g z/h z
    have hJ : J∈PuiseuxSector := by
      simpa only [J,div_eq_mul_inv] using puiseux_lowerSectorData.mul_mem hg (puiseux_lowerSectorData.inv_mem hh)
    have hJr := real_positive_quotient hgr hhr
    change ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re at hJr
    have hJray : ∀ᶠ t : ℝ in atTop,J (t:ℂ)≠0 := hJr.mono fun t ht he => by
      have hn := ht.2; rw [he,Complex.zero_re] at hn; exact lt_irrefl _ hn
    have hJnonzero : ¬ (fun t : ℝ => J (t:ℂ)) =ᶠ[atTop] fun _ => 0 := by
      intro he; obtain ⟨t,ht,h0⟩ := (hJray.and he).exists; exact ht h0
    have hJ0 := PuiseuxSector.ray_nonzero_to_sector hJ hJray
    have hJd := PuiseuxSector.log_deriv_tendsto hJ hJnonzero
    have hJm := PuiseuxSector.real_monotone hJ (hJr.mono fun _ h => h.1)
    obtain ⟨E,hE,hfactor⟩ := normalized_equal_exponent_ratio hg0 hh0 hFe hHe
    change ∀ᶠ z in sectorInfinity,F z/H z=J z*(1+E z) at hfactor
    have hbound : ∃ D : ℝ,∀ᶠ t : ℝ in atTop,‖F (t:ℂ)/H (t:ℂ)‖≤D := by
      obtain ⟨D,hD,hO⟩ := hO
      refine ⟨D,?_⟩
      filter_upwards [hFr,hHr,hO] with t hf hh ho
      have ef : F (t:ℂ)=((F (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hf.1)
      have eh : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hh.1)
      rw [ef,eh,←Complex.ofReal_div,Complex.norm_of_nonneg (div_pos hf.2 hh.2).le]
      exact (div_le_iff₀ hh.2).mpr ho
    obtain ⟨M,hM⟩ := lower_ratio_bounded hE hfactor hbound
    obtain ⟨c,hc,hJl,hJlim⟩ := PuiseuxSector.positive_bounded_limit hJ hJr
      ⟨M,hM.mono fun t ht => (Complex.re_le_norm (J (t:ℂ))).trans ht⟩
    obtain ⟨ε,C,hε,hC,he⟩ := hE.strip_bound
    rcases hc.eq_or_lt with hc | hc
    · subst c
      obtain ⟨hd0,hdd,hqa,hqn,hqd,hqr⟩ := PuiseuxSector.vanishing_ratio_data hJ hJr hJl
      obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := vanishing_equal_exponent_chart
        hbpos hε hC (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs
        (hs hJ.1) (hs hJ0) hJr (hJd.mono_left stripInfinity_le_sectorInfinity)
        (hdd.mono_left stripInfinity_le_sectorInfinity) hJl hJm (hs hqa) (hs hqn)
        (hqd.mono_left stripInfinity_le_sectorInfinity) hqr he (hs hfactor)
      refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
      intro ω S hω
      obtain ⟨η,R,hη,hm,hn,hsep⟩ := hmap ω S hω
      exact ⟨η,R,hη,hm,hn,fun _ => hsep⟩
    · have hlim : Tendsto (fun t : ℝ => F (t:ℂ)/H (t:ℂ)) atTop (𝓝 (c:ℂ)) := by
        have ht : Tendsto (fun z => J z*(1+E z)) sectorInfinity (𝓝 (c:ℂ)) := by
          simpa using hJlim.mul ((tendsto_const_nhds (x := (1:ℂ))).add hE.tendsto_zero)
        exact (ht.congr' (hfactor.mono fun _ h => h.symm)).comp tendsto_real_sectorInfinity
      have hnot : ¬ Tendsto (fun t : ℝ => F (t:ℂ)/H (t:ℂ)) atTop (𝓝 0) := by
        intro hz
        exact (Complex.ofReal_ne_zero.mpr hc.ne') (tendsto_nhds_unique hlim hz)
      have hdJ := PuiseuxSector.deriv_mem hJ
      rcases puiseux_lowerSectorData.zero_or_ne hdJ with hd0 | hdn
      · have hconst := strip_derivative_zero_constant (hs hJ.1) (hs hd0) (hJr.mono fun _ h => h.1) hJl
        have hf : ∀ᶠ z in stripInfinity,F z/H z=(c:ℂ)*(1+E z) := by
          filter_upwards [hs hfactor,hconst] with z hf hc; rwa [hc] at hf
        obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := constant_equal_exponent_chart
          hbpos hε hC hc (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs he hf
        refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
        intro ω S hω
        obtain ⟨η,R,hη,hm,hn⟩ := hmap ω S hω
        exact ⟨η,R,hη,hm,hn,fun h => False.elim (hnot h)⟩
      · have hdnray := tendsto_real_sectorInfinity.eventually hdn
        have hdd := PuiseuxSector.log_deriv_tendsto hdJ (by
          intro he; obtain ⟨t,ht,h0⟩ := (hdnray.and he).exists; exact ht h0)
        obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := positive_equal_exponent_chart
          hbpos hε hC hc (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs
          (hs hJ.1) (hs hJ0) (hJr.mono fun _ h => h.1) (hJd.mono_left stripInfinity_le_sectorInfinity)
          (hs hdn) (hdd.mono_left stripInfinity_le_sectorInfinity) hJl hJm he (hs hfactor)
        refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
        intro ω S hω
        obtain ⟨η,R,hη,hm,hn⟩ := hmap ω S hω
        exact ⟨η,R,hη,hm,hn,fun h => False.elim (hnot h)⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem ExpansionOver.positive_chart {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K)
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K) {F H : ℂ → ℂ}
    (hF : ExpansionOver K F) (hH : ExpansionOver K H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re)
    (htop : ∃ b : ℝ,0<b ∧ Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 (b:ℂ))) :
    PositiveExponentialChart F H := by
  obtain ⟨a,ha,g,hg,hg0,hgr,hFe,hFd⟩ := hF.positive_leading_strip hK hconj hFr hFt
  obtain ⟨b,hb,h,hh,hh0,hhr,hHe,hHd⟩ := hH.positive_leading_strip hK hconj hHr hHt
  obtain ⟨b',hb',hHd'⟩ := htop
  have heq : b=b' := Complex.ofReal_injective (tendsto_nhds_unique hHd hHd')
  have hbpos : 0<b := heq.symm ▸ hb'
  obtain ⟨_,_,hFs,_⟩ := hF
  obtain ⟨_,_,hHs,_⟩ := hH
  have hFa := hFs.eventually_analytic
  have hHa := hHs.eventually_analytic
  have hF0 := normalized_leading_nonzero hFe
  have hH0 := normalized_leading_nonzero hHe
  have hab : a≤b := unbounded_log_exponent_order hb
    (tendsto_real_sectorInfinity.eventually hFa) (tendsto_real_sectorInfinity.eventually hHa)
    hFr hHr hFt (hFd.comp tendsto_real_stripInfinity) (hHd.comp tendsto_real_stripInfinity) hO
  have hs {P : ℂ → Prop} (hp : ∀ᶠ z in sectorInfinity,P z) : ∀ᶠ z in stripInfinity,P z :=
    hp.filter_mono stripInfinity_le_sectorInfinity
  have hdfs := hFd
  have hdhs := hHd
  rcases hab.lt_or_eq with hab | hab
  · obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := strict_exponential_chart ha hab
      (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs
    refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
    intro ω S hω
    obtain ⟨η,R,hη,hm,hn,he⟩ := hmap ω S hω
    exact ⟨η,R,hη,hm,hn,fun _ => he⟩
  · subst a
    let J : ℂ → ℂ := fun z => g z/h z
    have hJ : J∈K := by
      simpa only [J,div_eq_mul_inv] using hK.mul_mem hg (hK.inv_mem hh)
    have hJr := real_positive_quotient hgr hhr
    change ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re at hJr
    have hJray : ∀ᶠ t : ℝ in atTop,J (t:ℂ)≠0 := hJr.mono fun t ht he => by
      have hn := ht.2; rw [he,Complex.zero_re] at hn; exact lt_irrefl _ hn
    have hJ0 := hK.ray_nonzero_to_sector hJ hJray
    have hJd := hK.log_deriv_strip hJ hJ0
    have hJm := hK.real_monotone hKd hJ (hJr.mono fun _ h => h.1)
    obtain ⟨E,hE,hfactor⟩ := normalized_equal_exponent_ratio hg0 hh0 hFe hHe
    change ∀ᶠ z in sectorInfinity,F z/H z=J z*(1+E z) at hfactor
    have hbound : ∃ D : ℝ,∀ᶠ t : ℝ in atTop,‖F (t:ℂ)/H (t:ℂ)‖≤D := by
      obtain ⟨D,hD,hO⟩ := hO
      refine ⟨D,?_⟩
      filter_upwards [hFr,hHr,hO] with t hf hh ho
      have ef : F (t:ℂ)=((F (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hf.1)
      have eh : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hh.1)
      rw [ef,eh,←Complex.ofReal_div,Complex.norm_of_nonneg (div_pos hf.2 hh.2).le]
      exact (div_le_iff₀ hh.2).mpr ho
    obtain ⟨M,hM⟩ := lower_ratio_bounded hE hfactor hbound
    obtain ⟨c,hc,hJl,hJlim⟩ := hK.positive_bounded_limit hKd hJ hJr
      ⟨M,hM.mono fun t ht => (Complex.re_le_norm (J (t:ℂ))).trans ht⟩
    obtain ⟨ε,C,hε,hC,he⟩ := hE.strip_bound
    rcases hc.eq_or_lt with hc | hc
    · subst c
      obtain ⟨hd0,hdd,hqa,hqn,hqd,hqr⟩ := hK.vanishing_ratio_data hKd hJ hJr hJl
      obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := vanishing_equal_exponent_chart
        hbpos hε hC (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs
        (hs (hK.analytic hJ)) (hs hJ0) hJr hJd
        hdd hJl hJm (hs hqa) (hs hqn)
        hqd hqr he (hs hfactor)
      refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
      intro ω S hω
      obtain ⟨η,R,hη,hm,hn,hsep⟩ := hmap ω S hω
      exact ⟨η,R,hη,hm,hn,fun _ => hsep⟩
    · have hlim : Tendsto (fun t : ℝ => F (t:ℂ)/H (t:ℂ)) atTop (𝓝 (c:ℂ)) := by
        have ht : Tendsto (fun t : ℝ => J (t:ℂ)*(1+E (t:ℂ))) atTop (𝓝 (c:ℂ)) := by
          simpa using hJlim.mul ((tendsto_const_nhds (x := (1:ℂ))).add (hE.tendsto_zero.comp tendsto_real_sectorInfinity))
        exact ht.congr' ((tendsto_real_sectorInfinity.eventually hfactor).mono fun _ h => h.symm)
      have hnot : ¬ Tendsto (fun t : ℝ => F (t:ℂ)/H (t:ℂ)) atTop (𝓝 0) := by
        intro hz
        exact (Complex.ofReal_ne_zero.mpr hc.ne') (tendsto_nhds_unique hlim hz)
      have hdJ := hKd _ hJ
      rcases hK.zero_or_ne hdJ with hd0 | hdn
      · have hconst := strip_derivative_zero_constant (hs (hK.analytic hJ)) (hs hd0) (hJr.mono fun _ h => h.1) hJl
        have hf : ∀ᶠ z in stripInfinity,F z/H z=(c:ℂ)*(1+E z) := by
          filter_upwards [hs hfactor,hconst] with z hf hc; rwa [hc] at hf
        obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := constant_equal_exponent_chart
          hbpos hε hC hc (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs he hf
        refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
        intro ω S hω
        obtain ⟨η,R,hη,hm,hn⟩ := hmap ω S hω
        exact ⟨η,R,hη,hm,hn,fun h => False.elim (hnot h)⟩
      · have hdnray := tendsto_real_sectorInfinity.eventually hdn
        have hdd := hK.log_deriv_strip hdJ hdn
        obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := positive_equal_exponent_chart
          hbpos hε hC hc (hs hFa) (hs hHa) (hs hF0) (hs hH0) hFr hHr hFt hHt hdfs hdhs
          (hs (hK.analytic hJ)) (hs hJ0) (hJr.mono fun _ h => h.1) hJd
          (hs hdn) hdd hJl hJm he (hs hfactor)
        refine ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,?_⟩
        intro ω S hω
        obtain ⟨η,R,hη,hm,hn⟩ := hmap ω S hω
        exact ⟨η,R,hη,hm,hn,fun h => False.elim (hnot h)⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem power_model_linear_sector {G : ℂ → ℂ} {a C K R : ℝ}
    (ha : 0 < a) (hC : 0 < C)
    (herr : ∀ z : ℂ, R < ‖z‖ → ‖G z-(C:ℂ)*z‖ ≤ K*‖z‖^(1-a))
    {ω : ℝ → ℝ} (hω : AdmissibleAngularLoss ω) (S : ℝ) :
    ∃ (η : ℝ → ℝ) (T : ℝ), AdmissibleAngularLoss η ∧
      ∀ z ∈ lossSector η T, G z ∈ lossSector ω S := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (max (2*C) (2/C)) (by norm_num : (1:ℝ)<2)
  have hkC : 2*C ≤ (2:ℝ)^k := (le_max_left _ _).trans hk.le
  have hkCi : 2/C ≤ (2:ℝ)^k := (le_max_right _ _).trans hk.le
  have hkdiv : 1/(2:ℝ)^k ≤ C/2 := by
    have hp : (0:ℝ)<2^k := by positivity
    rw [div_le_iff₀ hp]
    have hh := (div_le_iff₀ hC).mp hkCi
    nlinarith
  obtain ⟨hN,hup⟩ := hω.scale_envelope k
  let N := scaleEnvelope ω k
  let η : ℝ → ℝ := fun r => 16*N r
  have hη : AdmissibleAngularLoss η := hN.const_mul (by norm_num)
  have hηsmall := hη.tendsto_zero.eventually (eventually_lt_nhds (by linarith [Real.pi_pos] : (0:ℝ)<Real.pi/2))
  have hnorm := power_model_norm (q := 1) ha hC (by simpa using herr)
  have hescape : Tendsto (fun r : ℝ => C/2*r) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  obtain ⟨W,hW⟩ := eventually_atTop.mp hω.1
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hnorm.and (hup.and
    ((hN.power_absorption ha (K/C)).and ((hescape.eventually (eventually_gt_atTop (max W S))).and
    (hηsmall.and (hη.1.and (eventually_gt_atTop R)))))))
  refine ⟨η,T,hη,?_⟩
  intro z hz
  obtain ⟨hn,hu,he,hes,hηπ,hηp,hR⟩ := hT ‖z‖ hz.1.le
  have hb := hn.2 z rfl
  simp only [Real.rpow_one] at hb
  have hNk : ω ‖G z‖ ≤ N ‖z‖ := by
    apply hu
    constructor
    · calc
        ‖z‖/(2:ℝ)^k = (1/(2:ℝ)^k)*‖z‖ := by ring
        _ ≤ C/2*‖z‖ := mul_le_mul_of_nonneg_right hkdiv hn.1.le
        _ ≤ ‖G z‖ := hb.1
    · exact hb.2.trans (mul_le_mul_of_nonneg_right hkC hn.1.le)
  have hw := (hW _ ((le_max_left _ _).trans (hes.le.trans hb.1))).1
  have hnpos : 0 < N ‖z‖ := by dsimp [η] at hηp; nlinarith [hηp.1]
  have herror : ‖G z-(C:ℂ)*z‖ ≤ C*N ‖z‖*‖z‖ := by
    apply (herr z hR).trans
    have hmul := mul_le_mul_of_nonneg_left he (mul_pos hC hn.1).le
    rw [sub_eq_add_neg,Real.rpow_add hn.1,Real.rpow_one]
    field_simp at hmul
    nlinarith
  have hrelower := half_loss_norm_le_re hηp.1.le hηπ.le hz.2
  have hreerr := (abs_re_le_norm (G z-(C:ℂ)*z)).trans herror
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hreerr
  have hnormpos : 0 < ‖G z‖ := (mul_pos (by positivity) hn.1).trans_le hb.1
  refine ⟨(le_max_right _ _).trans_lt (hes.trans_le hb.1),
    arg_lt_of_re_lower hw (norm_pos_iff.mp hnormpos) ?_⟩
  have hm := mul_le_mul_of_nonneg_right hNk hnormpos.le
  have hmu := mul_le_mul_of_nonneg_left hb.2 hnpos.le
  have hrC := mul_le_mul_of_nonneg_left hrelower hC.le
  dsimp [η] at hrC
  nlinarith [(abs_le.mp hreerr).1,mul_pos (mul_pos hC hnpos) hn.1]

end DegeneratingTrees.Clock

 

 

 

open Filter Topology
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma power_exponent_le_one {f : ℝ → ℝ} {q C : ℝ} (hC : 0 < C)
    (hl : ∀ᶠ t : ℝ in atTop, C*t^q ≤ |f t|) (hO : f =O[atTop] id) : q ≤ 1 := by
  by_contra hq
  have hq : 0 < q-1 := by linarith
  obtain ⟨K,hK,hb⟩ := hO.exists_pos
  have ht := (tendsto_rpow_atTop hq).eventually (eventually_gt_atTop (K/C))
  obtain ⟨t,hl,hb,ht,ht0⟩ := (hl.and (hb.bound.and (ht.and (eventually_gt_atTop (0:ℝ))))).exists
  simp only [Real.norm_eq_abs,Function.id_def,abs_of_pos ht0] at hb
  have hpow : t^q = t^(q-1)*t := by
    calc
      t^q = t^((q-1)+1) := by congr 1; ring
      _ = t^(q-1)*t := by rw [Real.rpow_add ht0,Real.rpow_one]
  rw [hpow] at hl
  have hmul : K < C*t^(q-1) := by
    have := (div_lt_iff₀ hC).mp ht
    nlinarith
  nlinarith

lemma power_exponent_lt_one {f : ℝ → ℝ} {q C : ℝ} (hC : 0 < C)
    (hl : ∀ᶠ t : ℝ in atTop, C*t^q ≤ |f t|) (ho : f =o[atTop] id) : q < 1 := by
  by_contra hq
  have hq : 1 ≤ q := le_of_not_gt hq
  have hb := ho.bound (show 0 < C/2 by positivity)
  obtain ⟨t,hl,hb,ht1⟩ := (hl.and (hb.and (eventually_gt_atTop (1:ℝ)))).exists
  have ht0 : 0 < t := zero_lt_one.trans ht1
  simp only [Function.id_def,Real.norm_eq_abs,abs_of_pos ht0] at hb
  have hp : t ≤ t^q := by
    calc
      t = t^(1:ℝ) := (Real.rpow_one t).symm
      _ ≤ t^q := Real.rpow_le_rpow_of_exponent_le ht1.le hq
  have hh := mul_le_mul_of_nonneg_left hp hC.le
  nlinarith

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem Puiseux.sector_control {f : ℝ → ℝ}
    (hf : Puiseux (fun t => (f t:ℂ))) (ht : Tendsto f atTop atTop)
    (hO : f =O[atTop] id) :
    ∃ (G : ℂ → ℂ) (R : ℝ),
      (∀ z : ℂ, R < ‖z‖ → 0 < z.re → AnalyticAt ℂ G z) ∧
      (fun t => (f t:ℂ)) =ᶠ[atTop] (fun t => G (t:ℂ)) ∧
      (∀ z : ℂ, R < ‖z‖ → |f ‖z‖|/4 ≤ ‖G z‖ ∧ ‖G z‖ ≤ 4*|f ‖z‖|) ∧
      ∀ (ω : ℝ → ℝ) (S : ℝ), AdmissibleAngularLoss ω →
        ∃ (η : ℝ → ℝ) (T : ℝ), AdmissibleAngularLoss η ∧ R ≤ T ∧
          (∀ z ∈ lossSector η T, G z ∈ lossSector ω S) ∧
          (f =o[atTop] id → ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
            ∀ z ∈ lossSector η A, |(G z).re| ≤ ε*z.re) := by
  obtain ⟨q,a,C,K,R,G,hq,ha,hC,hK,hGa,he,herr⟩ := hf.positive_sector ht
  have hn := power_model_norm ha hC herr
  have hlo : ∀ᶠ r : ℝ in atTop, C/2*r^(q:ℝ) ≤ |f r| := by
    filter_upwards [hn,he] with r hr he
    have hh := (hr.2 (r:ℂ) (Complex.norm_of_nonneg hr.1.le)).1
    simpa only [←he,Complex.norm_real,Real.norm_eq_abs] using hh
  have hq1 : (q:ℝ) ≤ 1 := power_exponent_le_one (by positivity) hlo hO
  obtain ⟨W,hW⟩ := eventually_atTop.mp (hn.and he)
  let R' := max R W
  refine ⟨G,R',fun z hz => hGa z ((le_max_left _ _).trans_lt hz),he,?_,?_⟩
  · intro z hz
    obtain ⟨hn,he⟩ := hW ‖z‖ ((le_max_right _ _).trans hz.le)
    have hb := hn.2 z rfl
    have hb' := hn.2 (‖z‖:ℂ) (Complex.norm_of_nonneg hn.1.le)
    simp only [←he,Complex.norm_real,Real.norm_eq_abs] at hb'
    constructor <;> linarith
  · intro ω S hω
    have hmap : ∃ (η : ℝ → ℝ) (T : ℝ), AdmissibleAngularLoss η ∧
        ∀ z ∈ lossSector η T, G z ∈ lossSector ω S := by
      rcases lt_or_eq_of_le hq1 with hlt | heq
      · obtain ⟨T,hT⟩ := power_model_sublinear_sector hq hlt ha hC herr hω S
        exact ⟨ω,T,hω,hT⟩
      · exact power_model_linear_sector (K := K) (R := R) ha hC
          (by simpa only [heq,Complex.ofReal_one,Complex.cpow_one] using herr) hω S
    obtain ⟨η,T,hη,hT⟩ := hmap
    refine ⟨η,max R' T,hη,le_max_left _ _,?_,?_⟩
    · intro z hz
      exact hT z ⟨(le_max_right _ _).trans_lt hz.1,hz.2⟩
    · intro ho
      apply sublinear_sector_realpart (power_exponent_lt_one (by positivity) hlo ho)
        (show (0:ℝ)<2*C by positivity) _ hη
      exact hn.mono (fun r hr z hz => (hr.2 z hz).2)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 

def PositiveSectorControl (f : ℝ → ℝ) : Prop :=
  ∃ (G : ℂ → ℂ) (R : ℝ),
    (∀ z : ℂ, R < ‖z‖ → 0 < z.re → AnalyticAt ℂ G z) ∧
    (fun t => (f t:ℂ)) =ᶠ[atTop] (fun t => G (t:ℂ)) ∧
    (∀ z : ℂ, R < ‖z‖ → |f ‖z‖|/4 ≤ ‖G z‖ ∧ ‖G z‖ ≤ 4*|f ‖z‖|) ∧
    ∀ (ω : ℝ → ℝ) (S : ℝ), AdmissibleAngularLoss ω →
      ∃ (η : ℝ → ℝ) (T : ℝ), AdmissibleAngularLoss η ∧ R ≤ T ∧
        (∀ z ∈ lossSector η T, G z ∈ lossSector ω S) ∧
        (f =o[atTop] id → ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
          ∀ z ∈ lossSector η A, |(G z).re| ≤ ε*z.re)

theorem Puiseux.change_clock {H : ℝ → ℝ}
    (hH : Puiseux (fun t => (H t:ℂ))) (hHt : Tendsto H atTop atTop)
    (hfast : id =o[atTop] H) :
    ∃ I : ℝ → ℝ, Puiseux (fun t => (I t:ℂ)) ∧ Tendsto I atTop atTop ∧
      (∀ᶠ t in atTop, H (I t)=t) ∧ (∀ᶠ t in atTop, I (H t)=t) ∧
      I =o[atTop] id ∧ PositiveSectorControl I ∧
      ∀ f : ℝ → ℝ, Puiseux (fun t => (f t:ℂ)) → Tendsto f atTop atTop →
        f =O[atTop] H →
        PositiveSectorControl (fun t => f (I t)) ∧
        (f =o[atTop] H → (fun t => f (I t)) =o[atTop] id) := by
  obtain ⟨I,hI,hIt,hl,hr,hcomp⟩ := hH.change_coordinate hHt
  have hsmall : I =o[atTop] id := by
    apply (hfast.comp_tendsto hIt).congr' Filter.EventuallyEq.rfl
    exact hl
  refine ⟨I,hI,hIt,hl,hr,hsmall,hI.sector_control hIt hsmall.isBigO,?_⟩
  intro f hf hft hO
  have hO' : (fun t => f (I t)) =O[atTop] id := by
    apply (hO.comp_tendsto hIt).congr' Filter.EventuallyEq.rfl
    exact hl
  refine ⟨(hcomp _ hf).sector_control (hft.comp hIt) hO',?_⟩
  intro ho
  apply (ho.comp_tendsto hIt).congr' Filter.EventuallyEq.rfl
  exact hl

end DegeneratingTrees.Clock
end

end OAI
