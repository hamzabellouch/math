import Mathlib
import OAI.Analysis.PathSelection.RecursiveCharts

namespace OAI

/-! Second-clock multiplication, differentiation and transported sector fields. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma ClockGerm.finset_sum {xs : List (ℝ → ℝ)} {ι : Type*} (S : Finset ι)
    {f : ι → ℝ → ℂ} (h : ∀ i ∈ S,ClockGerm xs (f i)) :
    ClockGerm xs (fun t => ∑ i ∈ S,f i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ClockGerm.const xs 0
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem ClockGerm.mul {xs : List (ℝ → ℝ)} {f g : ℝ → ℂ}
    (hf : ClockGerm xs f) (hg : ClockGerm xs g) : ClockGerm xs (fun t => f t*g t) := by
  classical
  induction xs generalizing f g with
  | nil => exact Puiseux.mul hf hg
  | cons X xs ih =>
    obtain ⟨F,E,b,hF,hb,he⟩ := hf
    obtain ⟨G,D,c,hG,hc,he'⟩ := hg
    refine ⟨fun z => F z*G z,exponentSum E D,
      exponentConvolution hF.bounded_above hG.bounded_above hF.finite_above hG.finite_above b c,
      hF.mul hG (fun β hβ => hF.coefficient_slow hβ) (fun β hβ => hG.coefficient_slow hβ),?_,he.mul he'⟩
    intro δ _
    refine ⟨?_,convolution_analytic _ _ _ _ (fun β hβ => (hb β hβ).2) (fun β hβ => (hc β hβ).2) δ⟩
    apply ClockGerm.finset_sum
    intro p hp
    have hh := (exponentFiber_finite hF.bounded_above hG.bounded_above hF.finite_above hG.finite_above δ).mem_toFinset.mp hp
    exact ih (hb p.1 hh.1).1 (hc p.2 hh.2.1).1

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ValidClocks.second_lowerData {X Y : ℝ → ℝ} (hxs : ValidClocks [Y,X]) :
    ∃ K : Set (ℂ → ℂ),LowerSectorData K ∧
      ∀ b : ℂ → ℂ,(b∈K ↔
        (ClockGerm (X :: []) (fun t => b (Y t:ℂ)) ∧
          ∀ᶠ z in sectorInfinity,AnalyticAt ℂ b z)) := by
  have hxv := hxs.1
  obtain ⟨hxv',hY,hYt,hrel⟩ := hxs
  have hX : Puiseux (fun t => (X t:ℂ)) := hxv.2.1
  have hXt := hxv.2.2.1
  have hXc := hX.real_eventually_analytic.mono (fun _ h => h.continuousAt)
  have hYc := (hY.real_eventually_analytic hxv).mono (fun _ h => h.continuousAt)
  obtain ⟨H,hH,he⟩ := (firstClock_expansion_iff hX hXt).mp hY
  have hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re := by
    apply eventually_of_comp_clock hXt hXc
    filter_upwards [he,hYt.eventually (eventually_gt_atTop 0)] with t he hy
    rw [←he]
    exact ⟨rfl,hy⟩
  have hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro A
    apply eventually_of_comp_clock hXt hXc
    filter_upwards [he,hYt.eventually (eventually_ge_atTop A)] with t he hy
    change A≤(H (X t:ℂ)).re
    rwa [←he]
  have hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    apply eventually_of_comp_clock hXt hXc
    filter_upwards [he,hrel.def hε] with t he ht
    change ‖X t‖≤ε*‖(H (X t:ℂ)).re‖
    rwa [←he]
  obtain ⟨y,hya,hyr,hyt,hK⟩ := hH.lower_field_chart hHr hHt hfast
  have hyY : ∀ᶠ t : ℝ in atTop,y (Y t:ℂ)=(X t:ℂ) := by
    filter_upwards [he,hXt.eventually hyr] with t he hy
    rwa [he]
  refine ⟨TransportedFirstField y,hK,?_⟩
  intro b
  constructor
  · intro hb
    have hba := hK.analytic hb
    exact ⟨(transported_first_iff hX hXt hYt hYc (hya.mono fun _ h => h.1) hyt hyY hba).mp hb,hba⟩
  · rintro ⟨hb,hba⟩
    exact (transported_first_iff hX hXt hYt hYc (hya.mono fun _ h => h.1) hyt hyY hba).mpr hb

theorem ClockGerm.second_inv {X Y : ℝ → ℝ} (hxs : ValidClocks [Y,X])
    {f : ℝ → ℂ} (hf : ClockGerm [Y,X] f) :
    ClockGerm [Y,X] (fun t => (f t)⁻¹) := by
  obtain ⟨K,hK,hKm⟩ := hxs.second_lowerData
  obtain ⟨F,E,b,hF,hb,he⟩ := hf
  have hFK : ExpansionOver K F := ⟨E,b,hF,fun β hβ => (hKm _).mpr (hb β hβ)⟩
  obtain ⟨D,c,hF',hc⟩ := hFK.inv hK
  exact ⟨fun z => (F z)⁻¹,D,c,hF',fun β hβ => (hKm _).mp (hc β hβ),he.inv⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma transported_first_deriv_mem {H y : ℂ → ℂ}
    (hH : ExpansionOver PuiseuxSector H)
    (hya : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z ∧ H (y z)=z)
    (hyt : Tendsto y sectorInfinity sectorInfinity)
    {b : ℂ → ℂ} (hb : b∈TransportedFirstField y) :
    deriv b ∈ TransportedFirstField y := by
  obtain ⟨F,hF,he⟩ := hb
  let G : ℂ → ℂ := fun z => deriv F z*(deriv H z)⁻¹
  refine ⟨G,hF.puiseux_deriv.mul puiseux_lowerSectorData (hH.puiseux_deriv.inv puiseux_lowerSectorData),?_⟩
  have hid : (fun z => H (y z)) =ᶠ[sectorInfinity] id := hya.mono (fun _ h => h.2)
  have hder := sector_eventually_deriv_congr hid
  have heder := sector_eventually_deriv_congr he
  filter_upwards [heder,hder,hya,
    hyt.eventually hH.choose_spec.choose_spec.1.eventually_analytic,
    hyt.eventually hF.choose_spec.choose_spec.1.eventually_analytic] with z he hd hy hh hf
  have hchain := (hh.differentiableAt.hasDerivAt.comp z hy.1.differentiableAt.hasDerivAt).deriv
  have hprod : deriv H (y z)*deriv y z=1 := by
    change deriv (fun z => H (y z)) z=deriv H (y z)*deriv y z at hchain
    rw [←hchain,hd]
    simp
  have hn : deriv H (y z)≠0 := left_ne_zero_of_mul_eq_one hprod
  have hy' : deriv y z=(deriv H (y z))⁻¹ := by
    apply (mul_left_cancel₀ hn)
    rw [hprod,mul_inv_cancel₀ hn]
  rw [he]
  change deriv (F ∘ y) z=deriv F (y z)*(deriv H (y z))⁻¹
  rw [(hf.differentiableAt.hasDerivAt.comp z hy.1.differentiableAt.hasDerivAt).deriv,hy']

lemma ValidClocks.second_differentialData {X Y : ℝ → ℝ} (hxs : ValidClocks [Y,X]) :
    ∃ K : Set (ℂ → ℂ),LowerSectorData K ∧
      (∀ b : ℂ → ℂ,b∈K → deriv b∈K) ∧
      (∀ f : ℝ → ℂ,ClockGerm (X :: []) f → ∃ b : ℂ → ℂ,b∈K ∧ f =ᶠ[atTop] fun t => b (Y t:ℂ)) ∧
      ∀ b : ℂ → ℂ,(b∈K ↔
        (ClockGerm (X :: []) (fun t => b (Y t:ℂ)) ∧
          ∀ᶠ z in sectorInfinity,AnalyticAt ℂ b z)) := by
  have hxv := hxs.1
  obtain ⟨hxv',hY,hYt,hrel⟩ := hxs
  have hX : Puiseux (fun t => (X t:ℂ)) := hxv.2.1
  have hXt := hxv.2.2.1
  have hXc := hX.real_eventually_analytic.mono (fun _ h => h.continuousAt)
  have hYc := (hY.real_eventually_analytic hxv).mono (fun _ h => h.continuousAt)
  obtain ⟨H,hH,he⟩ := (firstClock_expansion_iff hX hXt).mp hY
  have hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re := by
    apply eventually_of_comp_clock hXt hXc
    filter_upwards [he,hYt.eventually (eventually_gt_atTop 0)] with t he hy
    rw [←he]
    exact ⟨rfl,hy⟩
  have hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro A
    apply eventually_of_comp_clock hXt hXc
    filter_upwards [he,hYt.eventually (eventually_ge_atTop A)] with t he hy
    change A≤(H (X t:ℂ)).re
    rwa [←he]
  have hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    apply eventually_of_comp_clock hXt hXc
    filter_upwards [he,hrel.def hε] with t he ht
    change ‖X t‖≤ε*‖(H (X t:ℂ)).re‖
    rwa [←he]
  obtain ⟨y,hya,hyr,hyt,hK⟩ := hH.lower_field_chart hHr hHt hfast
  have hyY : ∀ᶠ t : ℝ in atTop,y (Y t:ℂ)=(X t:ℂ) := by
    filter_upwards [he,hXt.eventually hyr] with t he hy
    rwa [he]
  refine ⟨TransportedFirstField y,hK,fun _ hb => transported_first_deriv_mem hH hya hyt hb,?_,?_⟩
  · intro f hf
    obtain ⟨F,hF,hef⟩ := (firstClock_expansion_iff hX hXt).mp hf
    refine ⟨fun z => F (y z),⟨F,hF,EventuallyEq.rfl⟩,?_⟩
    filter_upwards [hef,hyY] with t hef hy
    simpa only [hy] using hef
  intro b
  constructor
  · intro hb
    have hba := hK.analytic hb
    exact ⟨(transported_first_iff hX hXt hYt hYc (hya.mono fun _ h => h.1) hyt hyY hba).mp hb,hba⟩
  · rintro ⟨hb,hba⟩
    exact (transported_first_iff hX hXt hYt hYc (hya.mono fun _ h => h.1) hyt hyY hba).mpr hb

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma ClockGerm.second_of_lower {X Y : ℝ → ℝ} (hxs : ValidClocks [Y,X])
    {f : ℝ → ℂ} (hf : ClockGerm (X :: []) f) : ClockGerm [Y,X] f := by
  obtain ⟨K,hK,hKd,hKr,hKm⟩ := hxs.second_differentialData
  obtain ⟨b,hb,he⟩ := hKr f hf
  refine ⟨b,{0},fun _ => b,?_,fun _ _ => (hKm b).mp hb,he⟩
  simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using
    SectorExpansion.single 0 (hK.analytic hb) (hK.slow hb)

lemma ExpansionOver.deriv_mem {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K)
    {F : ℂ → ℂ} (hF : ExpansionOver K F) : ExpansionOver K (deriv F) := by
  obtain ⟨E,b,hF,hb⟩ := hF
  refine ⟨E,fun β z => (β:ℂ)*b β z+deriv (b β) z,
    hF.deriv (fun β hβ => hK.analytic (hb β hβ)),?_⟩
  intro β hβ
  exact hK.add_mem (hK.mul_mem (hK.const_mem (β:ℂ)) (hb β hβ)) (hKd _ (hb β hβ))

theorem ClockGerm.second_deriv {X Y : ℝ → ℝ} (hxs : ValidClocks [Y,X])
    {f : ℝ → ℂ} (hf : ClockGerm [Y,X] f) : ClockGerm [Y,X] (deriv f) := by
  obtain ⟨K,hK,hKd,hKr,hKm⟩ := hxs.second_differentialData
  obtain ⟨F,E,b,hF,hb,he⟩ := hf
  have hF' : ExpansionOver K (deriv F) :=
    (show ExpansionOver K F from ⟨E,b,hF,fun β hβ => (hKm _).mpr (hb β hβ)⟩).deriv_mem hK hKd
  have hFx : ClockGerm [Y,X] (fun t => deriv F (Y t:ℂ)) := by
    obtain ⟨D,c,hF',hc⟩ := hF'
    exact ⟨deriv F,D,c,hF',fun β hβ => (hKm _).mp (hc β hβ),EventuallyEq.rfl⟩
  have hYa := hxs.2.1.real_eventually_analytic hxs.1
  have hY' : ClockGerm (X :: []) (fun t => ((deriv Y t:ℝ):ℂ)) := by
    apply (hxs.2.1.first_deriv hxs.1.2.1 hxs.1.2.2.1).congr
    filter_upwards [hYa] with t ht
    exact ht.differentiableAt.hasDerivAt.ofReal_comp.deriv
  apply (hFx.mul (hY'.second_of_lower hxs)).congr
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  filter_upwards [hYa,
    hxs.2.2.1.eventually (tendsto_real_sectorInfinity.eventually hF.eventually_analytic),
    eventually_gt_atTop T] with t hYa hFa ht
  have hd := hFa.differentiableAt.hasDerivAt.comp_ofReal.scomp t hYa.differentiableAt.hasDerivAt
  have hc : (fun s => F (Y s:ℂ)) =ᶠ[𝓝 t] f :=
    (eventually_gt_nhds ht).mono (fun s hs => (hT s hs.le).symm)
  simpa only [Complex.real_smul,mul_comm] using (hd.congr_of_eventuallyEq hc.symm).deriv.symm

end DegeneratingTrees.Clock

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 
def TransportedField (K : Set (ℂ → ℂ)) (y : ℂ → ℂ) : Set (ℂ → ℂ) :=
  {b | ∃ F : ℂ → ℂ,ExpansionOver K F ∧ b =ᶠ[sectorInfinity] fun z => F (y z)}

lemma transported_lowerSectorData {K : Set (ℂ → ℂ)} (hK : LowerSectorData K) {y : ℂ → ℂ}
    (hya : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z)
    (hyt : Tendsto y sectorInfinity sectorInfinity)
    (hys : (fun z => (y z).re) =o[sectorInfinity] Complex.re) :
    LowerSectorData (TransportedField K y) := by
  constructor
  · intro c
    exact ⟨fun _ => c,ExpansionOver.const hK c,EventuallyEq.rfl⟩
  · rintro f g ⟨F,hF,he⟩ ⟨G,hG,he'⟩
    exact ⟨fun z => F z+G z,hF.add hK hG,he.add he'⟩
  · rintro f ⟨F,hF,he⟩
    exact ⟨fun z => -F z,hF.neg hK,he.neg⟩
  · rintro f g ⟨F,hF,he⟩ ⟨G,hG,he'⟩
    exact ⟨fun z => F z*G z,hF.mul hK hG,he.mul he'⟩
  · rintro f ⟨F,hF,he⟩
    exact ⟨fun z => (F z)⁻¹,hF.inv hK,he.inv⟩
  · rintro f ⟨F,hF,he⟩
    have hg : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => F (y w)) z := by
      filter_upwards [hya,hyt.eventually hF.choose_spec.choose_spec.1.eventually_analytic] with z hy hf
      exact hf.comp hy
    exact sector_eventually_analytic_congr hg he.symm
  · rintro f ⟨F,hF,he⟩
    obtain ⟨a,ha⟩ := hF.expBound_some
    intro ε hε
    exact (ha.comp_slow hyt hys ε hε).congr' he.symm Filter.EventuallyEq.rfl
  · rintro f ⟨F,hF,he⟩
    rcases hF.zero_or_ne hK with hz | hn
    · exact Or.inl (he.trans (hyt.eventually hz))
    · exact Or.inr ((he.and (hyt.eventually hn)).mono fun z h => by rw [h.1]; exact h.2)

lemma transported_deriv_mem {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K) {H y : ℂ → ℂ}
    (hH : ExpansionOver K H)
    (hya : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z ∧ H (y z)=z)
    (hyt : Tendsto y sectorInfinity sectorInfinity)
    {b : ℂ → ℂ} (hb : b∈TransportedField K y) :
    deriv b ∈ TransportedField K y := by
  obtain ⟨F,hF,he⟩ := hb
  let G : ℂ → ℂ := fun z => deriv F z*(deriv H z)⁻¹
  refine ⟨G,(hF.deriv_mem hK hKd).mul hK ((hH.deriv_mem hK hKd).inv hK),?_⟩
  have hid : (fun z => H (y z)) =ᶠ[sectorInfinity] id := hya.mono (fun _ h => h.2)
  have hder := sector_eventually_deriv_congr hid
  have heder := sector_eventually_deriv_congr he
  filter_upwards [heder,hder,hya,
    hyt.eventually hH.choose_spec.choose_spec.1.eventually_analytic,
    hyt.eventually hF.choose_spec.choose_spec.1.eventually_analytic] with z he hd hy hh hf
  have hchain := (hh.differentiableAt.hasDerivAt.comp z hy.1.differentiableAt.hasDerivAt).deriv
  have hprod : deriv H (y z)*deriv y z=1 := by
    change deriv (fun z => H (y z)) z=deriv H (y z)*deriv y z at hchain
    rw [←hchain,hd]
    simp
  have hn : deriv H (y z)≠0 := left_ne_zero_of_mul_eq_one hprod
  have hy' : deriv y z=(deriv H (y z))⁻¹ := by
    apply (mul_left_cancel₀ hn)
    rw [hprod,mul_inv_cancel₀ hn]
  rw [he]
  change deriv (F ∘ y) z=deriv F (y z)*(deriv H (y z))⁻¹
  rw [(hf.differentiableAt.hasDerivAt.comp z hy.1.differentiableAt.hasDerivAt).deriv,hy']

lemma tendsto_star_sectorInfinity : Tendsto (star : ℂ → ℂ) sectorInfinity sectorInfinity := by
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨ω,R,hω,hU⟩ := hU
  exact ⟨ω,R,hω,fun z hz => hU _ (mem_lossSector_star hz)⟩

lemma SectorInverse.reflection_eq {H y : ℂ → ℂ} {I : ℝ → ℝ} (hi : SectorInverse H y I) :
    (fun z => star (y (star z))) =ᶠ[sectorInfinity] y := by
  have ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => star (y (star w))) z := by
    filter_upwards [tendsto_star_sectorInfinity.eventually hi.analytic_left] with z hz
    exact analyticAt_reflection hz.1
  apply sector_analytic_eq_of_ray ha (hi.analytic_left.mono fun _ h => h.1)
  filter_upwards [hi.real_ray] with t ht
  simp only [Complex.star_def,Complex.conj_ofReal,ht]

lemma transported_conj_mem {K : Set (ℂ → ℂ)}
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K)
    {H y : ℂ → ℂ} {I : ℝ → ℝ} (hi : SectorInverse H y I)
    {b : ℂ → ℂ} (hb : b∈TransportedField K y) :
    (fun z => star (b (star z)))∈TransportedField K y := by
  obtain ⟨F,⟨E,c,hF,hc⟩,he⟩ := hb
  refine ⟨fun z => star (F (star z)),⟨E,fun β z => star (c β (star z)),
    hF.conj,fun β hβ => hconj _ (hc β hβ)⟩,?_⟩
  filter_upwards [tendsto_star_sectorInfinity.eventually he,hi.reflection_eq] with z he hy
  have hy' : y (star z)=star (y z) := by
    simpa only [star_star] using congrArg star hy
  simp only [he,hy']

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma SectorSlow.log_inverse {h : ℂ → ℂ} {I : ℝ → ℝ}
    (hs : SectorSlow h) (hIt : Tendsto I atTop atTop)
    (hi : ∀ᶠ t : ℝ in atTop,h (I t:ℂ)=(t:ℂ)) :
    Real.log =o[atTop] I := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨C,hC,hb⟩ := (hs (ε/2) (by positivity)).exists_pos
  have hbound := hIt.eventually (tendsto_real_sectorInfinity.eventually hb.bound)
  filter_upwards [hbound,hi,eventually_gt_atTop (1:ℝ),
    hIt.eventually (eventually_gt_atTop (0:ℝ)),
    hIt.eventually (eventually_ge_atTop (2*|Real.log C|/ε))] with t hb hi ht hI hIC
  have htpos : 0<t := by linarith
  have hb' : t≤C*Real.exp (ε/2*I t) := by
    simpa only [hi,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htpos,
      Complex.ofReal_re,abs_of_pos (Real.exp_pos _)] using hb
  have hl := Real.log_le_log htpos hb'
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne',Real.log_exp] at hl
  have hc : 2*|Real.log C|≤I t*ε := (div_le_iff₀ hε).mp hIC
  simp only [Real.norm_eq_abs,abs_of_pos (Real.log_pos ht),abs_of_pos hI]
  nlinarith [le_abs_self (Real.log C)]

lemma SectorInverse.log_small {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    {h y : ℂ → ℂ} {I : ℝ → ℝ} (hh : h∈K) (hi : SectorInverse h y I) :
    Real.log =o[atTop] I := by
  apply (hK.slow hh).log_inverse hi.ray_unbounded
  filter_upwards [hi.real_ray,tendsto_real_sectorInfinity.eventually hi.analytic_left] with t hr hl
  simpa only [hr] using hl.2

end DegeneratingTrees.Clock
end

end OAI
