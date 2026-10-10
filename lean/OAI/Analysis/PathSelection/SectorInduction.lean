import Mathlib
import OAI.Analysis.PathSelection.SecondClockFields

namespace OAI

/-! Transported lower charts, clock-sector induction and universal Hardy calculus. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma SectorInverse.original_ray {H y F b : ℂ → ℂ} {I : ℝ → ℝ}
    (hi : SectorInverse H y I)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (he : b =ᶠ[sectorInfinity] fun z => F (y z)) :
    ∀ᶠ t : ℝ in atTop,F (t:ℂ)=b (H (t:ℂ)) := by
  filter_upwards [hi.right,hHr,hHt.eventually (tendsto_real_sectorInfinity.eventually he)] with t hr hH he
  have eq : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hH)
  rw [←eq,hr] at he
  exact he.symm

lemma ScalarSectorChart.congr_composition {F x G y : ℂ → ℂ}
    (h : ScalarSectorChart F x)
    (he : (fun z => F (x z)) =ᶠ[sectorInfinity] (fun z => G (y z))) :
    ScalarSectorChart G y := by
  have hr := tendsto_real_sectorInfinity.eventually he
  obtain ⟨C,hC,hm⟩ := h.radial
  refine ⟨?_,h.unbounded.congr' (hr.mono fun _ e => congrArg Complex.re e),
    sector_eventually_analytic_congr h.analytic he,h.maps_sector.congr' he,C,hC,?_⟩
  · filter_upwards [h.positive,hr] with t ht he
    rwa [←he]
  · filter_upwards [hm,he,tendsto_norm_sectorInfinity.eventually hr] with z hm he hr
    rwa [he,hr] at hm

lemma transported_lowerSectorCharts {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hcharts : HasSectorCharts K) {H y : ℂ → ℂ} {I : ℝ → ℝ}
    (hH : ExpansionOver K H) (hi : SectorInverse H y I)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re))
    (hys : (fun z => (y z).re) =o[sectorInfinity] Complex.re) :
    LowerSectorCharts (TransportedField K y) := by
  have hL := transported_lowerSectorData hK (hi.analytic_left.mono fun _ h => h.1) hi.maps_sector hys
  intro h hh hhr hht hhfast
  obtain ⟨A,hA,hea⟩ := hh
  have hHr0 := hHr.mono fun _ h => h.1
  have hAH := hi.original_ray hHr0 hHt hea
  have hAHr : ∀ᶠ t : ℝ in atTop,A (t:ℂ)=h ((H (t:ℂ)).re:ℂ) := by
    filter_upwards [hAH,hHr] with t he hr
    exact he.trans (congrArg h (Complex.ext rfl (by simpa using hr.1)))
  have hAr : ∀ᶠ t : ℝ in atTop,(A (t:ℂ)).im=0 ∧ 0<(A (t:ℂ)).re := by
    filter_upwards [hAHr,hHt.eventually hhr] with t he hr
    rwa [he]
  have hAt : Tendsto (fun t : ℝ => (A (t:ℂ)).re) atTop atTop :=
    (hht.comp hHt).congr' (hAHr.mono fun _ e => (congrArg Complex.re e).symm)
  have hHA : (fun t : ℝ => (H (t:ℂ)).re) =o[atTop] (fun t : ℝ => (A (t:ℂ)).re) :=
    (hhfast.comp_tendsto hHt).congr' Filter.EventuallyEq.rfl
      (hAHr.mono fun _ e => (congrArg Complex.re e).symm)
  have hAfast : id =o[atTop] (fun t : ℝ => (A (t:ℂ)).re) := hfast.trans_isBigO hHA.isBigO
  obtain ⟨v,J,hvj,hfamily⟩ := hcharts A hA hAr hAt hAfast
  obtain ⟨hHv,hHvs⟩ := hfamily H hH hHr hHt hHA.isBigO
  let x : ℂ → ℂ := fun z => H (v z)
  let Q : ℝ → ℝ := fun t => (H (J t:ℂ)).re
  have hQt : Tendsto Q atTop atTop := hHt.comp hvj.ray_unbounded
  have hxreal : ∀ᶠ t : ℝ in atTop,x (t:ℂ)=(Q t:ℂ) := by
    filter_upwards [hvj.real_ray,hvj.ray_unbounded.eventually hHr] with t hv hr
    simp only [x,Q,hv]
    exact Complex.ext rfl (by simpa using hr.1)
  have hyx : (fun z => y (x z)) =ᶠ[sectorInfinity] v := by
    have ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => y (x w)) z := by
      filter_upwards [hHv.analytic,hHv.maps_sector.eventually hi.analytic_left] with z hx hy
      exact (show AnalyticAt ℂ y (x z) from hy.1).comp (f := x) hx
    apply sector_analytic_eq_of_ray ha (hvj.analytic_left.mono fun _ h => h.1)
    filter_upwards [hvj.real_ray,hvj.ray_unbounded.eventually hi.right] with t hv hr
    simpa only [x,hv] using hr
  have hax : (fun z => h (x z)) =ᶠ[sectorInfinity] (fun z => A (v z)) := by
    filter_upwards [hHv.maps_sector.eventually hea,hyx] with z he hy
    change h (x z)=A (y (x z)) at he
    simpa only [hy] using he
  have hxi : SectorInverse h x Q := by
    constructor
    · filter_upwards [hHv.analytic,hax,hvj.analytic_left] with z hx he hv
      exact ⟨hx,he.trans hv.2⟩
    · filter_upwards [tendsto_real_sectorInfinity.eventually hea,hi.real_ray,
        hi.ray_unbounded.eventually hvj.right,
        tendsto_real_sectorInfinity.eventually hi.analytic_left] with t he hir hvr hl
      change H (v (h (t:ℂ)))=(t:ℂ)
      rw [he,hir,hvr]
      simpa only [hir] using hl.2
    · exact hHv.maps_sector
    · exact hQt
    · exact hxreal
  refine ⟨x,Q,hxi,hxi.log_small hL ⟨A,hA,hea⟩,?_,?_⟩
  · obtain ⟨C,hC,hmod⟩ := hHv.radial
    refine ⟨max C 1,le_max_right _ _,?_⟩
    filter_upwards [hmod,tendsto_norm_sectorInfinity.eventually hxreal,
      tendsto_norm_sectorInfinity.eventually (hQt.eventually (eventually_gt_atTop (0:ℝ)))] with z hm he hq
    change ‖x (‖z‖:ℂ)‖/C≤‖x z‖ ∧ ‖x z‖≤C*‖x (‖z‖:ℂ)‖ at hm
    rw [he,Complex.norm_of_nonneg hq.le] at hm
    constructor
    · exact (div_le_div_of_nonneg_left hq.le hC (le_max_left C 1)).trans hm.1
    · exact hm.2.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) hq.le)
  · intro g hg hgr hgt hgo
    obtain ⟨B,hB,heb⟩ := hg
    have hBH := hi.original_ray hHr0 hHt heb
    have hBHr : ∀ᶠ t : ℝ in atTop,B (t:ℂ)=g ((H (t:ℂ)).re:ℂ) := by
      filter_upwards [hBH,hHr] with t he hr
      exact he.trans (congrArg g (Complex.ext rfl (by simpa using hr.1)))
    have hBr : ∀ᶠ t : ℝ in atTop,(B (t:ℂ)).im=0 ∧ 0<(B (t:ℂ)).re := by
      filter_upwards [hBHr,hHt.eventually hgr] with t he hr
      rwa [he]
    have hBt : Tendsto (fun t : ℝ => (B (t:ℂ)).re) atTop atTop :=
      (hgt.comp hHt).congr' (hBHr.mono fun _ e => (congrArg Complex.re e).symm)
    have hBA : (fun t : ℝ => (B (t:ℂ)).re) =O[atTop] (fun t : ℝ => (A (t:ℂ)).re) :=
      (hgo.comp_tendsto hHt).congr'
        (hBHr.mono fun _ e => (congrArg Complex.re e).symm)
        (hAHr.mono fun _ e => (congrArg Complex.re e).symm)
    obtain ⟨hBv,hBvs⟩ := hfamily B hB hBr hBt hBA
    have he : (fun z => B (v z)) =ᶠ[sectorInfinity] (fun z => g (x z)) := by
      filter_upwards [hHv.maps_sector.eventually heb,hyx] with z he hy
      change g (x z)=B (y (x z)) at he
      simpa only [hy] using he.symm
    refine ⟨hBv.congr_composition he,?_⟩
    intro hsmall
    have hsmall' : (fun t : ℝ => (B (t:ℂ)).re) =o[atTop] (fun t : ℝ => (A (t:ℂ)).re) :=
      (hsmall.comp_tendsto hHt).congr'
        (hBHr.mono fun _ e => (congrArg Complex.re e).symm)
        (hAHr.mono fun _ e => (congrArg Complex.re e).symm)
    exact (hBvs hsmall').congr' (he.mono fun _ e => congrArg Complex.re e) Filter.EventuallyEq.rfl

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ExpansionOver.of_lower {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    {F : ℂ → ℂ} (hF : F∈K) : ExpansionOver K F := by
  refine ⟨{0},fun _ => F,?_,fun _ _ => hF⟩
  simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using
    SectorExpansion.single 0 (hK.analytic hF) (hK.slow hF)

structure ClockSectorData (xs : List (ℝ → ℝ)) (X : ℝ → ℝ) (K : Set (ℂ → ℂ)) : Prop where
  lower : LowerSectorData K
  differential : ∀ b : ℂ → ℂ,b∈K → deriv b∈K
  reflection : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K
  charts : HasSectorCharts K
  coordinate : ExpansionOver K id
  represents : ∀ f : ℝ → ℂ,ClockGerm xs f → ∃ b : ℂ → ℂ,b∈K ∧ f =ᶠ[atTop] fun t => b (X t:ℂ)
  membership : ∀ b : ℂ → ℂ,b∈K ↔
    (ClockGerm xs (fun t => b (X t:ℂ)) ∧ ∀ᶠ z in sectorInfinity,AnalyticAt ℂ b z)

lemma ClockSectorData.expansion_iff {xs : List (ℝ → ℝ)} {X : ℝ → ℝ} {K : Set (ℂ → ℂ)}
    (hD : ClockSectorData xs X K) {f : ℝ → ℂ} :
    ClockGerm (X::xs) f ↔ ∃ F : ℂ → ℂ,ExpansionOver K F ∧ f =ᶠ[atTop] fun t => F (X t:ℂ) := by
  constructor
  · rintro ⟨F,E,b,hF,hb,he⟩
    exact ⟨F,⟨E,b,hF,fun β hβ => (hD.membership _).mpr (hb β hβ)⟩,he⟩
  · rintro ⟨F,⟨E,b,hF,hb⟩,he⟩
    exact ⟨F,E,b,hF,fun β hβ => (hD.membership _).mp (hb β hβ),he⟩

lemma puiseux_clockSectorData {X : ℝ → ℝ}
    (hX : Puiseux (fun t => (X t:ℂ))) (hXt : Tendsto X atTop atTop) :
    ClockSectorData [] X PuiseuxSector := by
  refine ⟨puiseux_lowerSectorData,fun _ hb => PuiseuxSector.deriv_mem hb,?_,
    puiseux_hasSectorCharts,ExpansionOver.puiseux_mem ⟨Eventually.of_forall fun _ => analyticAt_id,puiseux_variable⟩,?_,?_⟩
  · intro b hb
    refine ⟨?_,?_⟩
    · filter_upwards [tendsto_star_sectorInfinity.eventually hb.1] with z hz
      exact analyticAt_reflection hz
    · simpa only [Complex.star_def,Complex.conj_ofReal] using hb.2.conj
  · intro f hf
    obtain ⟨I,hI,hIt,hl,hr⟩ := hX.inverse_change hXt
    obtain ⟨F,hF,he⟩ := (hf.comp_unbounded hI hIt).sector_representative
    refine ⟨F,hF,?_⟩
    filter_upwards [hXt.eventually he,hr] with t he hr
    simpa only [hr] using he
  · intro b
    constructor
    · intro hb
      exact ⟨hb.2.comp_unbounded hX hXt,hb.1⟩
    · rintro ⟨hb,hba⟩
      exact ⟨hba,puiseux_of_comp_clock hX hXt hb⟩

lemma ClockSectorData.step {xs : List (ℝ → ℝ)} {X Y : ℝ → ℝ} {K : Set (ℂ → ℂ)}
    (hD : ClockSectorData xs X K) (hvalid : ValidClocks (Y::X::xs)) :
    ∃ L : Set (ℂ → ℂ),ClockSectorData (X::xs) Y L := by
  have hXt := hvalid.1.2.2.1
  have hYt := hvalid.2.2.1
  have hXc := (hvalid.1.2.1.real_eventually_analytic hvalid.1.1).mono (fun _ h => h.continuousAt)
  have hYc := (hvalid.2.1.real_eventually_analytic hvalid.1).mono (fun _ h => h.continuousAt)
  obtain ⟨H,hH,he⟩ := hD.expansion_iff.mp hvalid.2.1
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
    filter_upwards [he,hvalid.2.2.2.def hε] with t he ht
    change ‖X t‖≤ε*‖(H (X t:ℂ)).re‖
    rwa [←he]
  obtain ⟨y,I,hi,hfamily⟩ := hD.charts H hH hHr hHt hfast
  have hir : ∀ᶠ t : ℝ in atTop,(id (t:ℂ)).im=0 ∧ 0<(id (t:ℂ)).re := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact ⟨rfl,ht⟩
  have hys := (hfamily id hD.coordinate hir tendsto_id hfast.isBigO).2 hfast
  have hL := transported_lowerSectorData hD.lower (hi.analytic_left.mono fun _ h => h.1) hi.maps_sector hys
  have hLd := fun b hb => transported_deriv_mem hD.lower hD.differential hH hi.analytic_left hi.maps_sector (b := b) hb
  have hLc := fun b hb => transported_conj_mem hD.reflection hi (b := b) hb
  have hLcharts := lowerSectorData_hasSectorCharts hL hLd hLc
    (transported_lowerSectorCharts hD.lower hD.charts hH hi hHr hHt hfast hys)
  have hyY : ∀ᶠ t : ℝ in atTop,y (Y t:ℂ)=(X t:ℂ) := by
    filter_upwards [he,hXt.eventually hi.right] with t he hy
    rwa [he]
  refine ⟨TransportedField K y,⟨hL,hLd,hLc,hLcharts,?_,?_,?_⟩⟩
  · apply ExpansionOver.of_lower hL
    exact ⟨H,hH,hi.analytic_left.mono fun _ h => h.2.symm⟩
  · intro f hf
    obtain ⟨F,hF,hef⟩ := hD.expansion_iff.mp hf
    refine ⟨fun z => F (y z),⟨F,hF,EventuallyEq.rfl⟩,?_⟩
    filter_upwards [hef,hyY] with t hef hy
    simpa only [hy] using hef
  · intro b
    constructor
    · rintro ⟨F,hF,heb⟩
      refine ⟨hD.expansion_iff.mpr ⟨F,hF,?_⟩,hL.analytic ⟨F,hF,heb⟩⟩
      filter_upwards [hYt.eventually (tendsto_real_sectorInfinity.eventually heb),hyY] with t he hy
      simpa only [hy] using he
    · rintro ⟨hb,hba⟩
      obtain ⟨F,hF,heb⟩ := hD.expansion_iff.mp hb
      refine ⟨F,hF,?_⟩
      have hfa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => F (y w)) z := by
        filter_upwards [hi.analytic_left,hi.maps_sector.eventually hF.choose_spec.choose_spec.1.eventually_analytic] with z hy hf
        exact hf.comp hy.1
      apply sector_analytic_eq_of_ray hba hfa
      apply eventually_of_comp_clock hYt hYc
      filter_upwards [heb,hyY] with t he hy
      simpa only [hy] using he

 
theorem ValidClocks.sectorData {xs : List (ℝ → ℝ)} {X : ℝ → ℝ}
    (hvalid : ValidClocks (X::xs)) : ∃ K : Set (ℂ → ℂ),ClockSectorData xs X K := by
  induction xs generalizing X with
  | nil => exact ⟨PuiseuxSector,puiseux_clockSectorData hvalid.2.1 hvalid.2.2.1⟩
  | cons Y ys ih =>
    obtain ⟨K,hK⟩ := ih hvalid.1
    exact hK.step hvalid

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ClockGerm.of_lower {xs : List (ℝ → ℝ)} {X : ℝ → ℝ}
    (hvalid : ValidClocks (X::xs)) {f : ℝ → ℂ} (hf : ClockGerm xs f) :
    ClockGerm (X::xs) f := by
  obtain ⟨K,hK⟩ := hvalid.sectorData
  obtain ⟨b,hb,he⟩ := hK.represents f hf
  exact hK.expansion_iff.mpr ⟨b,ExpansionOver.of_lower hK.lower hb,he⟩

 

theorem ClockGerm.inv {xs : List (ℝ → ℝ)} (hvalid : ValidClocks xs)
    {f : ℝ → ℂ} (hf : ClockGerm xs f) : ClockGerm xs (fun t => (f t)⁻¹) := by
  cases xs with
  | nil => exact Puiseux.inv hf
  | cons X xs =>
    obtain ⟨K,hK⟩ := hvalid.sectorData
    obtain ⟨F,hF,he⟩ := hK.expansion_iff.mp hf
    exact hK.expansion_iff.mpr ⟨fun z => (F z)⁻¹,hF.inv hK.lower,he.inv⟩

 

theorem ClockGerm.deriv {xs : List (ℝ → ℝ)} (hvalid : ValidClocks xs)
    {f : ℝ → ℂ} (hf : ClockGerm xs f) : ClockGerm xs (_root_.deriv f) := by
  induction xs generalizing f with
  | nil => exact Puiseux.deriv hf
  | cons X xs ih =>
    obtain ⟨K,hK⟩ := hvalid.sectorData
    obtain ⟨F,hF,he⟩ := hK.expansion_iff.mp hf
    have hFa := hF.choose_spec.choose_spec.1.eventually_analytic
    have hFx : ClockGerm (X::xs) (fun t => _root_.deriv F (X t:ℂ)) :=
      hK.expansion_iff.mpr ⟨_root_.deriv F,hF.deriv_mem hK.lower hK.differential,EventuallyEq.rfl⟩
    have hXa := hvalid.2.1.real_eventually_analytic hvalid.1
    have hX' : ClockGerm xs (fun t => ((_root_.deriv X t:ℝ):ℂ)) := by
      apply (ih hvalid.1 hvalid.2.1).congr
      filter_upwards [hXa] with t ht
      exact ht.differentiableAt.hasDerivAt.ofReal_comp.deriv
    apply (hFx.mul (hX'.of_lower hvalid)).congr
    obtain ⟨T,hT⟩ := eventually_atTop.mp he
    filter_upwards [hXa,hvalid.2.2.1.eventually (tendsto_real_sectorInfinity.eventually hFa),
      eventually_gt_atTop T] with t hXa hFa ht
    have hd := hFa.differentiableAt.hasDerivAt.comp_ofReal.scomp t hXa.differentiableAt.hasDerivAt
    have hc : (fun s => F (X s:ℂ)) =ᶠ[𝓝 t] f :=
      (eventually_gt_nhds ht).mono (fun s hs => (hT s hs.le).symm)
    simpa only [Complex.real_smul,mul_comm] using (hd.congr_of_eventuallyEq hc.symm).deriv.symm

lemma ClockGerm.real_deriv {xs : List (ℝ → ℝ)} (hvalid : ValidClocks xs)
    {f : ℝ → ℝ} (hf : ClockGerm xs (fun t => (f t:ℂ))) :
    ClockGerm xs (fun t => ((_root_.deriv f t:ℝ):ℂ)) := by
  apply (hf.deriv hvalid).congr
  filter_upwards [hf.real_eventually_analytic hvalid] with t ht
  exact ht.differentiableAt.hasDerivAt.ofReal_comp.deriv

 
theorem ClockGerm.real_derivative_sign {xs : List (ℝ → ℝ)} (hvalid : ValidClocks xs)
    {f : ℝ → ℝ} (hf : ClockGerm xs (fun t => (f t:ℂ))) :
    (_root_.deriv f =ᶠ[atTop] 0) ∨ (∀ᶠ t : ℝ in atTop,0<_root_.deriv f t) ∨
      (∀ᶠ t : ℝ in atTop,_root_.deriv f t<0) := by
  by_cases hz : _root_.deriv f =ᶠ[atTop] 0
  · exact Or.inl hz
  · exact Or.inr ((hf.real_deriv hvalid).eventually_sign hvalid hz)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma LogMonomial.rat_mul {xs : List (ℝ → ℝ)} {M : ℝ → ℝ}
    (hM : LogMonomial xs M) (q : ℚ) :
    LogMonomial xs (fun t => (q:ℝ)*M t) := by
  induction hM with
  | base p =>
    convert LogMonomial.base (q*p) using 1
    funext t
    push_cast
    ring
  | @step xs M X hM β ih =>
    convert LogMonomial.step (X := X) ih ((q:ℝ)*β) using 1
    funext t
    ring

lemma puiseux_exp_rat_log (q : ℚ) :
    Puiseux (fun t => (Real.exp ((q:ℝ)*Real.log t):ℂ)) := by
  refine ⟨q.den,q.den_pos,-q.num,fun _ => 1,analyticAt_const,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  simp only [Complex.real_smul,mul_one,rootCoord_zpow ht]
  have hq : -((-q.num:ℤ):ℝ)/(q.den:ℝ)=(q:ℝ) := by
    push_cast
    simpa only [neg_neg] using (Rat.cast_def (K := ℝ) q).symm
  rw [hq,Real.rpow_def_of_pos ht,mul_comm]

lemma ClockGerm.exp_clock {X : ℝ → ℝ} (xs : List (ℝ → ℝ)) (β : ℝ) :
    ClockGerm (X::xs) (fun t => (Real.exp (β*X t):ℂ)) := by
  have hs : SectorSlow (fun _ : ℂ => (1:ℂ)) := fun _ hε => (ExpBound.const 1).mono hε.le
  have ha : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) z :=
    Eventually.of_forall (fun _ => analyticAt_const)
  refine ⟨fun z => Complex.exp ((β:ℂ)*z)*1,{β},fun _ _ => 1,
    SectorExpansion.single β ha hs,?_,?_⟩
  · exact fun _ _ => ⟨ClockGerm.const xs 1,SectorEventually.truth.mono (fun _ _ => analyticAt_const)⟩
  · exact Eventually.of_forall (fun t => by simp [←Complex.ofReal_mul,Complex.ofReal_exp])

 

lemma LogMonomial.exp_mem {xs : List (ℝ → ℝ)} {M : ℝ → ℝ}
    (hM : LogMonomial xs M) (hxs : ValidClocks xs) :
    ClockGerm xs (fun t => (Real.exp (M t):ℂ)) := by
  induction hM with
  | base p => exact puiseux_exp_rat_log p
  | @step xs M X hM β ih =>
    apply ((ClockGerm.exp_clock xs β).mul ((ih hxs.1).of_lower hxs)).congr
    exact Eventually.of_forall (fun t => by
      simp only [Real.exp_add,Complex.ofReal_mul])

 

theorem ClockGerm.divisible_size {xs : List (ℝ → ℝ)} (hxs : ValidClocks xs)
    {f : ℝ → ℂ} (hf : ClockGerm xs f) (hne : ¬ f =ᶠ[atTop] 0)
    (n : ℕ) (hn : 0<n) :
    ∃ ρ : ℝ → ℝ, ClockGerm xs (fun t => (ρ t:ℂ)) ∧
      (∀ t,0<ρ t) ∧ ∃ c : ℝ,0<c ∧
      Tendsto (fun t => (ρ t)^n / ‖f t‖) atTop (𝓝 c) := by
  obtain ⟨M,hM,d,hd,ht⟩ := hf.leading hxs hne
  let q : ℚ := (n:ℚ)⁻¹
  have hq : (q:ℝ)=(n:ℝ)⁻¹ := by simp [q]
  refine ⟨fun t => Real.exp ((q:ℝ)*M t),(hM.rat_mul q).exp_mem hxs,
    fun t => Real.exp_pos _,‖d‖⁻¹,inv_pos.mpr (norm_pos_iff.mpr hd),?_⟩
  apply (ht.norm.inv₀ (norm_ne_zero_iff.mpr hd)).congr'
  filter_upwards [] with t
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le]
  rw [←Real.exp_nat_mul]
  have hmul : (n:ℝ)*((q:ℝ)*M t)=M t := by
    rw [hq,←mul_assoc,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')]
    simp
  rw [hmul,Real.exp_neg,mul_inv_rev,inv_inv,div_eq_mul_inv,mul_comm]

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 

theorem ClockGerm.eventually_monotone {xs : List (ℝ → ℝ)}
    (hvalid : ValidClocks xs) {f : ℝ → ℝ}
    (hf : ClockGerm xs (fun t => (f t:ℂ))) :
    ∃ T : ℝ, (∃ c : ℝ, ∀ t ∈ Ioi T,f t=c) ∨
      StrictMonoOn f (Ioi T) ∨ StrictAntiOn f (Ioi T) := by
  have ha := hf.real_eventually_analytic hvalid
  rcases hf.real_derivative_sign hvalid with hz | hp | hn
  · obtain ⟨T,hT⟩ := eventually_atTop.mp (ha.and hz)
    have hd : DifferentiableOn ℝ f (interior (Ioi T)) := by
      intro t ht
      exact (hT t (interior_subset ht).le).1.differentiableAt.differentiableWithinAt
    have hc : ContinuousOn f (Ioi T) := fun t ht => (hT t ht.le).1.continuousAt.continuousWithinAt
    have hm := monotoneOn_of_deriv_nonneg (convex_Ioi T) hc hd
      (fun t ht => (hT t (interior_subset ht).le).2.ge)
    have hn := antitoneOn_of_deriv_nonpos (convex_Ioi T) hc hd
      (fun t ht => (hT t (interior_subset ht).le).2.le)
    refine ⟨T,Or.inl ⟨f (T+1),fun t ht => ?_⟩⟩
    have ht1 : T+1 ∈ Ioi T := by simp
    rcases le_total t (T+1) with h | h
    · exact le_antisymm (hm ht ht1 h) (hn ht ht1 h)
    · exact le_antisymm (hn ht1 ht h) (hm ht1 ht h)
  · obtain ⟨T,hT⟩ := eventually_atTop.mp (ha.and hp)
    refine ⟨T,Or.inr (Or.inl ?_)⟩
    exact strictMonoOn_of_deriv_pos (convex_Ioi T)
      (fun t ht => (hT t ht.le).1.continuousAt.continuousWithinAt)
      (fun t ht => (hT t (interior_subset ht).le).2)
  · obtain ⟨T,hT⟩ := eventually_atTop.mp (ha.and hn)
    refine ⟨T,Or.inr (Or.inr ?_)⟩
    exact strictAntiOn_of_deriv_neg (convex_Ioi T)
      (fun t ht => (hT t ht.le).1.continuousAt.continuousWithinAt)
      (fun t ht => (hT t (interior_subset ht).le).2)

end DegeneratingTrees.Clock
end

end OAI
