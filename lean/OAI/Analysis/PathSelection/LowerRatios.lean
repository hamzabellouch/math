import Mathlib
import OAI.Analysis.PathSelection.InverseAsymptotics
import OAI.Analysis.PathSelection.RealClocks

namespace OAI

/-! Lower Hardy fields, vanishing Puiseux ratios and leading-term comparison. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma PuiseuxSector.real_puiseux {J : ℂ → ℂ} (hJ : J∈PuiseuxSector)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0) :
    Puiseux (fun t : ℝ => ((J (t:ℂ)).re:ℂ)) := by
  apply hJ.2.congr
  filter_upwards [hr] with t ht
  exact Complex.ext rfl (by simpa using ht)

lemma sector_real_derivative {J : ℂ → ℂ}
    (ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ J z)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0) :
    ∀ᶠ t : ℝ in atTop,deriv J (t:ℂ)=((deriv (fun s : ℝ => (J (s:ℂ)).re) t:ℝ):ℂ) := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp hr
  filter_upwards [tendsto_real_sectorInfinity.eventually ha,eventually_gt_atTop A] with t ht hAt
  have him := analytic_ray_deriv_im_zero hAt ht (fun s hs => hA s hs.le)
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht.differentiableAt.hasDerivAt.comp_ofReal
  apply Complex.ext
  · exact hd.deriv.symm
  · simpa using him

lemma eventually_monotone_bounded_limit {f : ℝ → ℝ}
    (hm : ∃ A : ℝ,MonotoneOn f (Ici A) ∨ AntitoneOn f (Ici A))
    (hb : ∃ M : ℝ,∀ᶠ t : ℝ in atTop,|f t|≤M) :
    ∃ c : ℝ,Tendsto f atTop (𝓝 c) := by
  obtain ⟨A,hA⟩ := hm
  obtain ⟨M,hM⟩ := hb
  obtain ⟨B,hB⟩ := eventually_atTop.mp hM
  let C := max A B
  let g : ℝ → ℝ := fun t => f (max C t)
  have hg (t : ℝ) : |g t|≤M := hB _ ((le_max_right A B).trans (le_max_left C t))
  have he : g =ᶠ[atTop] f := (eventually_ge_atTop C).mono (fun t ht => by simp [g,max_eq_right ht])
  rcases hA with hA | hA
  · have hm' : Monotone g := fun s t hst => hA
      ((le_max_left A B).trans (le_max_left C s))
      ((le_max_left A B).trans (le_max_left C t)) (max_le_max_left C hst)
    have hb' : BddAbove (range g) := ⟨M,by rintro _ ⟨t,rfl⟩; exact (abs_le.mp (hg t)).2⟩
    exact ⟨_,(tendsto_atTop_ciSup hm' hb').congr' he⟩
  · have hm' : Antitone g := fun s t hst => hA
      ((le_max_left A B).trans (le_max_left C s))
      ((le_max_left A B).trans (le_max_left C t)) (max_le_max_left C hst)
    have hb' : BddBelow (range g) := ⟨-M,by rintro _ ⟨t,rfl⟩; exact (abs_le.mp (hg t)).1⟩
    exact ⟨_,(tendsto_atTop_ciInf hm' hb').congr' he⟩

lemma PuiseuxSector.real_monotone {J : ℂ → ℂ} (hJ : J∈PuiseuxSector)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0) :
    ∃ A : ℝ,MonotoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) := by
  obtain ⟨A,hA⟩ := (PuiseuxSector.real_puiseux hJ hr).eventually_monotone
  have hsub : Ici (A+1)⊆Ioi A := fun t ht => by change A+1≤t at ht; change A<t; linarith
  exact ⟨A+1,hA.imp (fun h => h.mono hsub) (fun h => h.mono hsub)⟩

lemma PuiseuxSector.positive_bounded_limit {J : ℂ → ℂ} (hJ : J∈PuiseuxSector)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re)
    (hb : ∃ M : ℝ,∀ᶠ t : ℝ in atTop,(J (t:ℂ)).re≤M) :
    ∃ c : ℝ,0≤c ∧ Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 c) ∧
      Tendsto J sectorInfinity (𝓝 (c:ℂ)) := by
  obtain ⟨M,hM⟩ := hb
  obtain ⟨c,hc⟩ := eventually_monotone_bounded_limit (PuiseuxSector.real_monotone hJ (hr.mono fun _ h => h.1))
    ⟨M,by filter_upwards [hr,hM] with t ht hm; rwa [abs_of_pos ht.2]⟩
  have hc0 : 0≤c := ge_of_tendsto hc (hr.mono fun _ h => h.2.le)
  exact ⟨c,hc0,hc,PuiseuxSector.tendsto_of_ray hJ (complex_real_limit (hr.mono fun _ h => h.1) hc)⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma positive_vanishing_not_deriv_nonneg {f : ℝ → ℝ}
    (ha : ∀ᶠ t : ℝ in atTop,AnalyticAt ℝ f t)
    (hp : ∀ᶠ t : ℝ in atTop,0<f t)
    (ht : Tendsto f atTop (𝓝 0)) :
    ¬ (∀ᶠ t : ℝ in atTop,0≤_root_.deriv f t) := by
  intro hn
  obtain ⟨A,hA⟩ := eventually_atTop.mp (ha.and (hp.and hn))
  have hm : MonotoneOn f (Ioi A) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi A)
    · exact fun x hx => (hA x hx.le).1.continuousAt.continuousWithinAt
    · exact fun x hx => (hA x (interior_subset hx).le).1.differentiableAt.differentiableWithinAt
    · exact fun x hx => (hA x (interior_subset hx).le).2.2
  have hh : f (A+1)≤0 := ge_of_tendsto ht ((eventually_ge_atTop (A+1)).mono fun t ht =>
    hm (by change A<A+1; linarith) (by change A<t; linarith) ht)
  exact (not_lt_of_ge hh) (hA (A+1) (by linarith)).2.1

lemma Puiseux.positive_vanishing_derivative_negative {f : ℝ → ℝ}
    (hf : Puiseux (fun t => (f t:ℂ)))
    (hp : ∀ᶠ t : ℝ in atTop,0<f t) (ht : Tendsto f atTop (𝓝 0)) :
    ∀ᶠ t : ℝ in atTop,_root_.deriv f t<0 := by
  have hn := positive_vanishing_not_deriv_nonneg hf.real_eventually_analytic hp ht
  have hne : ¬ _root_.deriv f =ᶠ[atTop] fun _ => 0 := fun he => hn (he.mono (fun _ h => by rw [h]))
  rcases hf.real_deriv.eventually_sign hne with hs | hs
  · exact False.elim (hn (hs.mono fun _ h => h.le))
  · exact hs

lemma PuiseuxSector.ray_nonzero_to_sector {J : ℂ → ℂ} (hJ : J∈PuiseuxSector)
    (hn : ∀ᶠ t : ℝ in atTop,J (t:ℂ)≠0) : ∀ᶠ z in sectorInfinity,J z≠0 := by
  rcases puiseux_lowerSectorData.zero_or_ne hJ with hz | hz
  · obtain ⟨t,ht,h0⟩ := (hn.and (tendsto_real_sectorInfinity.eventually hz)).exists
    exact False.elim (ht h0)
  · exact hz

lemma PuiseuxSector.vanishing_ratio_data {J : ℂ → ℂ} (hJ : J∈PuiseuxSector)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re)
    (ht : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 0)) :
    (∀ᶠ z in sectorInfinity,deriv J z≠0) ∧
    Tendsto (fun z => deriv (deriv J) z/deriv J z) sectorInfinity (𝓝 0) ∧
    (∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => deriv J z/J z) z) ∧
    (∀ᶠ z in sectorInfinity,deriv J z/J z≠0) ∧
    Tendsto (fun z => deriv (fun z => deriv J z/J z) z/(deriv J z/J z)) sectorInfinity (𝓝 0) ∧
    (∀ᶠ t : ℝ in atTop,(deriv J (t:ℂ)/J (t:ℂ)).im=0 ∧ (deriv J (t:ℂ)/J (t:ℂ)).re<0) := by
  have hd := PuiseuxSector.deriv_mem hJ
  have hD := sector_real_derivative hJ.1 (hr.mono fun _ h => h.1)
  have hneg := (PuiseuxSector.real_puiseux hJ (hr.mono fun _ h => h.1)).positive_vanishing_derivative_negative
    (hr.mono fun _ h => h.2) ht
  have hdr : ∀ᶠ t : ℝ in atTop,deriv J (t:ℂ)≠0 := by
    filter_upwards [hD,hneg] with t hd hn
    rw [hd]
    exact Complex.ofReal_ne_zero.mpr hn.ne
  have hdn := PuiseuxSector.ray_nonzero_to_sector hd hdr
  have hqr : ∀ᶠ t : ℝ in atTop,(deriv J (t:ℂ)/J (t:ℂ)).im=0 ∧
      (deriv J (t:ℂ)/J (t:ℂ)).re<0 := by
    filter_upwards [hr,hD,hneg] with t hr hd hn
    have he : J (t:ℂ)=((J (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr.1)
    rw [hd,he,←Complex.ofReal_div]
    exact ⟨rfl,div_neg_of_neg_of_pos hn hr.2⟩
  have hq : (fun z => deriv J z/J z)∈PuiseuxSector := by
    simpa only [div_eq_mul_inv] using puiseux_lowerSectorData.mul_mem hd (puiseux_lowerSectorData.inv_mem hJ)
  have hqnray : ∀ᶠ t : ℝ in atTop,deriv J (t:ℂ)/J (t:ℂ)≠0 := hqr.mono fun t ht he => by
    have hh := ht.2; rw [he,Complex.zero_re] at hh; exact lt_irrefl _ hh
  have hqn := PuiseuxSector.ray_nonzero_to_sector hq hqnray
  have hneq {f : ℂ → ℂ} (hn : ∀ᶠ t : ℝ in atTop,f (t:ℂ)≠0) :
      ¬ (fun t : ℝ => f (t:ℂ)) =ᶠ[atTop] fun _ => 0 := by
    intro he; obtain ⟨t,ht,h0⟩ := (hn.and he).exists; exact ht h0
  exact ⟨hdn,PuiseuxSector.log_deriv_tendsto hd (hneq hdr),hq.1,hqn,
    PuiseuxSector.log_deriv_tendsto hq (hneq (f := fun z => deriv J z/J z) hqnray),hqr⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma real_nonzero_eventually_sign {f : ℝ → ℝ}
    (hc : ∀ᶠ t : ℝ in atTop,ContinuousAt f t)
    (hn : ∀ᶠ t : ℝ in atTop,f t≠0) :
    (∀ᶠ t : ℝ in atTop,0<f t) ∨ (∀ᶠ t : ℝ in atTop,f t<0) := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hc.and hn)
  have hcont : ContinuousOn f (Ici A) := fun t ht => (hA t ht).1.continuousWithinAt
  have hpos (u : ℝ) (hu : A≤u) (hp : 0<f u) : ∀ t : ℝ,A≤t → 0<f t := by
    intro t ht
    by_contra he
    have he : f t≤0 := le_of_not_gt he
    obtain ⟨v,hv,hfv⟩ := isPreconnected_Ici.intermediate_value ht hu hcont ⟨he,hp.le⟩
    exact (hA v hv).2 hfv
  rcases (hA A le_rfl).2.lt_or_gt with hm | hp
  · right
    filter_upwards [eventually_ge_atTop A] with t ht
    by_contra he
    have hp : 0<f t := lt_of_le_of_ne (le_of_not_gt he) (Ne.symm (hA t ht).2)
    exact (not_lt_of_ge hm.le) (hpos t ht hp A le_rfl)
  · exact Or.inl ((eventually_ge_atTop A).mono fun t ht => hpos A le_rfl hp t ht)

lemma LowerSectorData.ray_nonzero_to_sector {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    {J : ℂ → ℂ} (hJ : J∈K) (hn : ∀ᶠ t : ℝ in atTop,J (t:ℂ)≠0) :
    ∀ᶠ z in sectorInfinity,J z≠0 := by
  rcases hK.zero_or_ne hJ with hz | hz
  · obtain ⟨t,ht,h0⟩ := (hn.and (tendsto_real_sectorInfinity.eventually hz)).exists
    exact False.elim (ht h0)
  · exact hz

lemma LowerSectorData.real_derivative_sign {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K)
    {J : ℂ → ℂ} (hJ : J∈K) (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0) :
    (∀ᶠ t : ℝ in atTop,0≤deriv (fun s : ℝ => (J (s:ℂ)).re) t) ∨
    (∀ᶠ t : ℝ in atTop,deriv (fun s : ℝ => (J (s:ℂ)).re) t<0) := by
  have he := sector_real_derivative (hK.analytic hJ) hr
  rcases hK.zero_or_ne (hKd _ hJ) with hz | hn
  · left
    filter_upwards [he,tendsto_real_sectorInfinity.eventually hz] with t ht hz
    have hz' : deriv (fun s : ℝ => (J (s:ℂ)).re) t=0 :=
      Complex.ofReal_eq_zero.mp (ht.symm.trans hz)
    rw [hz']
  · have hdn : ∀ᶠ t : ℝ in atTop,(deriv J (t:ℂ)).re≠0 := by
      filter_upwards [he,tendsto_real_sectorInfinity.eventually hn] with t ht hn
      rw [ht] at hn ⊢
      exact Complex.ofReal_ne_zero.mp hn
    have hdc : ∀ᶠ t : ℝ in atTop,ContinuousAt (fun t : ℝ => (deriv J (t:ℂ)).re) t := by
      filter_upwards [tendsto_real_sectorInfinity.eventually (hK.analytic (hKd _ hJ))] with t ht
      exact Complex.continuous_re.continuousAt.comp
        (ht.continuousAt.comp Complex.continuous_ofReal.continuousAt)
    rcases real_nonzero_eventually_sign hdc hdn with hp | hm
    · left
      filter_upwards [he,hp] with t ht hp
      simpa only [ht,Complex.ofReal_re] using hp.le
    · right
      filter_upwards [he,hm] with t ht hm
      rwa [ht] at hm

lemma LowerSectorData.real_monotone {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K)
    {J : ℂ → ℂ} (hJ : J∈K) (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0) :
    ∃ A : ℝ,MonotoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) ∨
      AntitoneOn (fun t : ℝ => (J (t:ℂ)).re) (Ici A) := by
  have ha : ∀ᶠ t : ℝ in atTop,AnalyticAt ℝ (fun t : ℝ => (J (t:ℂ)).re) t := by
    filter_upwards [tendsto_real_sectorInfinity.eventually (hK.analytic hJ)] with t ht
    exact (Complex.reCLM.analyticAt _).comp ((ht.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt _))
  rcases hK.real_derivative_sign hKd hJ hr with hp | hm
  · obtain ⟨A,hA⟩ := eventually_atTop.mp (ha.and hp)
    refine ⟨A,Or.inl ?_⟩
    apply monotoneOn_of_deriv_nonneg (convex_Ici A)
    · exact fun t ht => (hA t ht).1.continuousAt.continuousWithinAt
    · exact fun t ht => (hA t (interior_subset ht)).1.differentiableAt.differentiableWithinAt
    · exact fun t ht => (hA t (interior_subset ht)).2
  · obtain ⟨A,hA⟩ := eventually_atTop.mp (ha.and hm)
    refine ⟨A,Or.inr ?_⟩
    apply antitoneOn_of_deriv_nonpos (convex_Ici A)
    · exact fun t ht => (hA t ht).1.continuousAt.continuousWithinAt
    · exact fun t ht => (hA t (interior_subset ht)).1.differentiableAt.differentiableWithinAt
    · exact fun t ht => (hA t (interior_subset ht)).2.le

lemma LowerSectorData.positive_bounded_limit {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K)
    {J : ℂ → ℂ} (hJ : J∈K)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re)
    (hb : ∃ M : ℝ,∀ᶠ t : ℝ in atTop,(J (t:ℂ)).re≤M) :
    ∃ c : ℝ,0≤c ∧ Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 c) ∧
      Tendsto (fun t : ℝ => J (t:ℂ)) atTop (𝓝 (c:ℂ)) := by
  obtain ⟨M,hM⟩ := hb
  obtain ⟨c,hc⟩ := eventually_monotone_bounded_limit (hK.real_monotone hKd hJ (hr.mono fun _ h => h.1))
    ⟨M,by filter_upwards [hr,hM] with t ht hm; rwa [abs_of_pos ht.2]⟩
  exact ⟨c,ge_of_tendsto hc (hr.mono fun _ h => h.2.le),hc,complex_real_limit (hr.mono fun _ h => h.1) hc⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma LowerSectorData.vanishing_ratio_data {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K) {J : ℂ → ℂ} (hJ : J∈K)
    (hr : ∀ᶠ t : ℝ in atTop,(J (t:ℂ)).im=0 ∧ 0<(J (t:ℂ)).re)
    (ht : Tendsto (fun t : ℝ => (J (t:ℂ)).re) atTop (𝓝 0)) :
    (∀ᶠ z in sectorInfinity,deriv J z≠0) ∧
    Tendsto (fun z => deriv (deriv J) z/deriv J z) stripInfinity (𝓝 0) ∧
    (∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => deriv J z/J z) z) ∧
    (∀ᶠ z in sectorInfinity,deriv J z/J z≠0) ∧
    Tendsto (fun z => deriv (fun z => deriv J z/J z) z/(deriv J z/J z)) stripInfinity (𝓝 0) ∧
    (∀ᶠ t : ℝ in atTop,(deriv J (t:ℂ)/J (t:ℂ)).im=0 ∧ (deriv J (t:ℂ)/J (t:ℂ)).re<0) := by
  have hd := hKd _ hJ
  have hD := sector_real_derivative (hK.analytic hJ) (hr.mono fun _ h => h.1)
  have hneg : ∀ᶠ t : ℝ in atTop,deriv (fun s : ℝ => (J (s:ℂ)).re) t<0 := by
    have ha : ∀ᶠ t : ℝ in atTop,AnalyticAt ℝ (fun s : ℝ => (J (s:ℂ)).re) t := by
      filter_upwards [tendsto_real_sectorInfinity.eventually (hK.analytic hJ)] with t ht
      exact (Complex.reCLM.analyticAt _).comp ((ht.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt _))
    exact (hK.real_derivative_sign hKd hJ (hr.mono fun _ h => h.1)).resolve_left
      (positive_vanishing_not_deriv_nonneg ha (hr.mono fun _ h => h.2) ht)
  have hdr : ∀ᶠ t : ℝ in atTop,deriv J (t:ℂ)≠0 := by
    filter_upwards [hD,hneg] with t hd hn
    rw [hd]
    exact Complex.ofReal_ne_zero.mpr hn.ne
  have hdn := hK.ray_nonzero_to_sector hd hdr
  have hqr : ∀ᶠ t : ℝ in atTop,(deriv J (t:ℂ)/J (t:ℂ)).im=0 ∧
      (deriv J (t:ℂ)/J (t:ℂ)).re<0 := by
    filter_upwards [hr,hD,hneg] with t hr hd hn
    have he : J (t:ℂ)=((J (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr.1)
    rw [hd,he,←Complex.ofReal_div]
    exact ⟨rfl,div_neg_of_neg_of_pos hn hr.2⟩
  have hq : (fun z => deriv J z/J z)∈K := by
    simpa only [div_eq_mul_inv] using hK.mul_mem hd (hK.inv_mem hJ)
  have hqnray : ∀ᶠ t : ℝ in atTop,deriv J (t:ℂ)/J (t:ℂ)≠0 := hqr.mono fun t ht he => by
    have hh := ht.2; rw [he,Complex.zero_re] at hh; exact lt_irrefl _ hh
  have hqn := hK.ray_nonzero_to_sector hq hqnray
  exact ⟨hdn,hK.log_deriv_strip hd hdn,hK.analytic hq,hqn,
    hK.log_deriv_strip hq hqn,hqr⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma ExpSmall.relative_quotient {f g : ℂ → ℂ} (hf : ExpSmall 0 f) (hg : ExpSmall 0 g) :
    ExpSmall 0 (fun z => (1+f z)/(1+g z)-1) := by
  have hi : ExpBound 0 (fun z => (1+g z)⁻¹) := by
    apply ExpBound.of_tendsto (c := 1)
    simpa using (tendsto_const_nhds.add hg.tendsto_zero).inv₀ (by norm_num : (1:ℂ)+0≠0)
  have hn : ∀ᶠ z in sectorInfinity,1+g z≠0 := by
    have ht : Tendsto (fun z => 1+g z) sectorInfinity (𝓝 1) := by simpa using tendsto_const_nhds.add hg.tendsto_zero
    exact ht.eventually_ne (by norm_num : (1:ℂ)≠0)
  have hh := (hf.sub hg).mul hi
  simp only [add_zero] at hh
  apply hh.congr
  filter_upwards [hn] with z hz
  field_simp
  ring

lemma normalized_equal_exponent_ratio {F H g h : ℂ → ℂ} {b : ℝ}
    (hg : ∀ᶠ z in sectorInfinity,g z≠0) (hh : ∀ᶠ z in sectorInfinity,h z≠0)
    (hF : ExpSmall 0 (fun z => Complex.exp (((-b:ℝ):ℂ)*z)*(g z)⁻¹*F z-1))
    (hH : ExpSmall 0 (fun z => Complex.exp (((-b:ℝ):ℂ)*z)*(h z)⁻¹*H z-1)) :
    ∃ E : ℂ → ℂ,ExpSmall 0 E ∧
      ∀ᶠ z in sectorInfinity,F z/H z=(g z/h z)*(1+E z) := by
  let f := fun z => Complex.exp (((-b:ℝ):ℂ)*z)*(g z)⁻¹*F z-1
  let k := fun z => Complex.exp (((-b:ℝ):ℂ)*z)*(h z)⁻¹*H z-1
  refine ⟨fun z => (1+f z)/(1+k z)-1,hF.relative_quotient hH,?_⟩
  filter_upwards [hg,hh] with z hgz hhz
  dsimp only [f,k]
  have hc (a : ℂ) : 1+(a-1)=a := by ring
  simp only [hc]
  by_cases hz : H z=0
  · simp [hz]
  · field_simp [hgz,hhz,hz,Complex.exp_ne_zero]

lemma lower_ratio_bounded {F H J E : ℂ → ℂ}
    (he : ExpSmall 0 E)
    (hfactor : ∀ᶠ z in sectorInfinity,F z/H z=J z*(1+E z))
    (hbound : ∃ M : ℝ,∀ᶠ t : ℝ in atTop,‖F (t:ℂ)/H (t:ℂ)‖≤M) :
    ∃ M : ℝ,∀ᶠ t : ℝ in atTop,‖J (t:ℂ)‖≤M := by
  obtain ⟨M,hM⟩ := hbound
  have hEt : Tendsto (fun t : ℝ => ‖E (t:ℂ)‖) atTop (𝓝 0) := by
    simpa only [norm_zero,Function.comp_def] using ((he.tendsto_zero.norm).comp tendsto_real_sectorInfinity)
  have hE := hEt.eventually (eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num))
  refine ⟨2*M,?_⟩
  filter_upwards [hM,hE,tendsto_real_sectorInfinity.eventually hfactor] with t ht heq hf
  have hl : 1/2≤‖1+E (t:ℂ)‖ := by
    have hh : (1:ℝ)≤‖1+E (t:ℂ)‖+‖E (t:ℂ)‖ := by
      calc
        1 = ‖(1+E (t:ℂ))-E (t:ℂ)‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    nlinarith
  rw [hf,norm_mul] at ht
  nlinarith [norm_nonneg (J (t:ℂ))]

end DegeneratingTrees.Clock
end

end OAI
