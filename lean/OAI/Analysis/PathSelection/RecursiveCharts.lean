import Mathlib
import OAI.Analysis.PathSelection.FirstLevelCharts

namespace OAI

/-! General common charts, second-clock charts and slowly varying coefficients. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem ExpansionOver.zero_chart {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K)
    (hcharts : LowerSectorCharts K) {F H : ℂ → ℂ}
    (hF : ExpansionOver K F) (hH : ExpansionOver K H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re))
    (htop : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 0)) :
    ∃ (y : ℂ → ℂ) (I : ℝ → ℝ),SectorInverse H y I ∧ ScalarSectorChart F y ∧
      ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
        (fun z => (F (y z)).re) =o[sectorInfinity] Complex.re) := by
  obtain ⟨g,h,hg,hh,hne,hgr,hhr,hgt,hht,hhfast,hgo,hFe,hHe,hgo'⟩ :=
    hF.zero_leading_strip_data hK hconj hH hFr hHr hFt hHt hO hfast htop
  obtain ⟨x,I,hxi,hlog,⟨C,hC,hxmod⟩,hfamily⟩ := hcharts h hh hhr hht hhfast
  obtain ⟨hGi,hGs⟩ := hfamily g hg hgr hgt hgo
  have hxa := hxi.analytic_left
  have hxt := hxi.maps_sector
  have hIt := hxi.ray_unbounded
  have hxright := hxi.right
  have hxr : ∀ᶠ t : ℝ in atTop,x (t:ℂ)=(I t:ℂ) ∧ h (I t:ℂ)=(t:ℂ) := by
    filter_upwards [hxi.real_ray,tendsto_real_sectorInfinity.eventually hxa] with t hr hl
    exact ⟨hr,by simpa only [hr] using hl.2⟩
  have hGa := hGi.analytic
  have hGt := hGi.maps_sector
  obtain ⟨M,hM,hGmod⟩ := hGi.radial
  obtain ⟨ε,L,hε,hL,hErr⟩ := hFe.common_sector_bound hHe
  have hFa := hF.choose_spec.choose_spec.1.eventually_analytic
  have hHa := hH.choose_spec.choose_spec.1.eventually_analytic
  let G : ℂ → ℂ := fun z => g (x z)
  let E : ℂ → ℂ := fun z => F (x z)/g (x z)-1
  let P : ℂ → ℂ := fun z => H (x z)
  have hPa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ P z := by
    filter_upwards [hxa,hxt.eventually hHa] with z hx hh
    exact hh.comp hx.1
  have hPr : ∀ᶠ t : ℝ in atTop,(P (t:ℂ)).im=0 := by
    filter_upwards [hxr,hIt.eventually hHr] with t hx hh
    simpa only [P,hx.1] using hh.1
  have hPt : Tendsto (fun t : ℝ => (P (t:ℂ)).re) atTop atTop :=
    (hHt.comp hIt).congr' (hxr.mono fun t ht => by simp only [P,ht.1,Function.comp_apply])
  have hEa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ E z := by
    filter_upwards [hxa,hxt.eventually hFa,hxt.eventually (hK.analytic hg),hxt.eventually hne] with z hx hf hg hn
    exact ((hf.comp hx.1).div (hg.comp hx.1) hn.1).sub analyticAt_const
  have hPe : ∀ᶠ z in sectorInfinity,‖P z-z‖≤L*‖z‖*Real.exp (-ε*(x z).re) := by
    filter_upwards [hxa,hxt.eventually hErr,hxt.eventually hne] with z hx he hn
    have heq : P z-z=z*(H (x z)/h (x z)-1) := by
      calc
        P z-z=H (x z)-h (x z) := by rw [hx.2]
        _=h (x z)*(H (x z)/h (x z)-1) := by field_simp [hn.2]
        _=z*(H (x z)/h (x z)-1) := by rw [hx.2]
    rw [heq,norm_mul]
    exact (mul_le_mul_of_nonneg_left he.2 (norm_nonneg z)).trans_eq (by ring)
  have hEe : ∀ᶠ z in sectorInfinity,‖E z‖≤L*Real.exp (-ε*(x z).re) :=
    (hxt.eventually hErr).mono fun _ he => he.1
  obtain ⟨D,hD,hDb⟩ := hgo.exists_pos
  have hGr : ∀ᶠ t : ℝ in atTop,‖G (t:ℂ)‖≤D*|t| := by
    filter_upwards [hxr,hIt.eventually hDb.bound,hIt.eventually hgr] with t hx hd hg
    have eh : (h (I t:ℂ)).re=t := congrArg Complex.re hx.2
    have eg : g (I t:ℂ)=((g (I t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hg.1)
    change ‖g (x (t:ℂ))‖≤D*|t|
    rw [hx.1,eg,Complex.norm_real,Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs,eh] using hd
  have hGu : ∀ᶠ z in sectorInfinity,‖G z‖≤(M*D)*‖z‖ := by
    filter_upwards [hGmod,tendsto_norm_sectorInfinity.eventually hGr] with z hm hr
    have hr' : ‖g (x (‖z‖:ℂ))‖≤D*‖z‖ := by simpa only [abs_of_nonneg (norm_nonneg _)] using hr
    exact hm.2.trans (by nlinarith)
  obtain ⟨v,J,hva,hvt,hJt,hvr,hvright,hfva,hfvt,hfvm,hfsep⟩ :=
    zero_exponent_chart hPa hPr hC hL hε hIt
      hlog hxmod hxt hPe hGa hEa hGt
      (show (0:ℝ)≤M*D by positivity) hGu hM hGmod hEe
  let y : ℂ → ℂ := fun z => x (v z)
  let Q : ℂ → ℂ := fun z => G (v z)*(1+E (v z))
  have hyt : Tendsto y sectorInfinity sectorInfinity := hxt.comp hvt
  have hyr : ∀ᶠ t : ℝ in atTop,y (t:ℂ)=(I (J t):ℂ) := by
    filter_upwards [hvr,hJt.eventually hxr] with t hv hx
    simp only [y,hv.1,hx.1]
  have hQt : ∀ᶠ z in sectorInfinity,Q z=F (y z) := by
    filter_upwards [hyt.eventually hne] with z hz
    dsimp [Q,G,E,y]
    have hn : g (x (v z))≠0 := hz.1
    field_simp [hn]
    ring
  have hvrightC : ∀ᶠ t : ℝ in atTop,v (P (t:ℂ))=(t:ℂ) := by
    filter_upwards [hvright,hPr,hPt.eventually hvr] with t hi hp hv
    have he : P (t:ℂ)=((P (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hp)
    rw [he,hv.1,hi]
  have hyrt : ∀ᶠ t : ℝ in atTop,y (H (t:ℂ))=(t:ℂ) := by
    filter_upwards [hxright,hht.eventually hvrightC,hhr] with t hx hv hh
    have eh : h (t:ℂ)=((h (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hh.1)
    have hp : P (h (t:ℂ))=H (t:ℂ) := by simp only [P,hx]
    rw [←eh,hp] at hv
    dsimp [y]
    rw [hv,hx]
  have hIJt := hIt.comp hJt
  refine ⟨y,fun t => I (J t),⟨?_,hyrt,hyt,hIJt,hyr⟩,⟨?_,?_,?_,hfvt.congr' hQt,4*M,by positivity,?_⟩,?_⟩
  · filter_upwards [hva,hvt.eventually hxa] with z hv hx
    exact ⟨hx.1.comp hv.1,hv.2⟩
  · filter_upwards [hyr,hIJt.eventually hFr] with t hy hf
    simpa only [hy,Function.comp_apply] using hf
  · exact (hFt.comp hIJt).congr' (hyr.mono fun t hy => by simp only [hy,Function.comp_apply])
  · filter_upwards [hva,hvt.eventually hxa,hyt.eventually hFa] with z hv hx hf
    exact hf.comp (hx.1.comp hv.1)
  · filter_upwards [hfvm,hQt,tendsto_norm_sectorInfinity.eventually (tendsto_real_sectorInfinity.eventually hQt)] with z hm he hr
    change ‖Q (‖z‖:ℂ)‖/(4*M)≤‖Q z‖ ∧ ‖Q z‖≤(4*M)*‖Q (‖z‖:ℂ)‖ at hm
    simpa only [he,hr] using hm
  · intro hsmall
    have hGsmall := hGs (hgo' hsmall)
    exact (hfsep hGsmall).congr' (hQt.mono fun _ he => congrArg Complex.re he) Filter.EventuallyEq.rfl

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ExpansionOver.scalar_chart {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K)
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K)
    (hcharts : LowerSectorCharts K) {F H : ℂ → ℂ}
    (hF : ExpansionOver K F) (hH : ExpansionOver K H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : (fun t : ℝ => (F (t:ℂ)).re) =O[atTop] (fun t : ℝ => (H (t:ℂ)).re))
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re)) :
    ∃ (y : ℂ → ℂ) (I : ℝ → ℝ),SectorInverse H y I ∧ ScalarSectorChart F y ∧
      ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
        (fun z => (F (y z)).re) =o[sectorInfinity] Complex.re) := by
  obtain ⟨b,hb,g,hg,hg0,hgr,hHe,hHd⟩ := hH.positive_leading_strip hK hconj hHr hHt
  have hO' := real_positive_bigO (hFr.mono fun _ h => h.2) (hHr.mono fun _ h => h.2) hO
  rcases hb.eq_or_lt with hb | hb
  · have hzero : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 0) := by
      simpa only [←hb,Complex.ofReal_zero] using hHd
    exact hF.zero_chart hK hconj hcharts hH hFr hHr hFt hHt hO' hfast hzero
  · obtain ⟨y,I,ha,hr,ht,hIt,hreal,hFr',hFt',hFa,hm,hn,hs⟩ :=
      (hF.positive_chart hK hKd hconj hH hFr hHr hFt hHt hO' ⟨b,hb,hHd⟩).sector
        (hFr.mono fun _ h => h.1) (hHr.mono fun _ h => h.1)
    exact ⟨y,I,⟨ha,hr,ht,hIt,hreal⟩,⟨hFr',hFt',hFa,hm,16,by norm_num,hn⟩,hs⟩

lemma ScalarSectorChart.congr_inverse {F x y : ℂ → ℂ}
    (h : ScalarSectorChart F x) (he : x =ᶠ[sectorInfinity] y) :
    ScalarSectorChart F y := by
  have hf : (fun z => F (x z)) =ᶠ[sectorInfinity] (fun z => F (y z)) :=
    he.mono fun _ ht => congrArg F ht
  have hr := tendsto_real_sectorInfinity.eventually hf
  obtain ⟨C,hC,hm⟩ := h.radial
  refine ⟨?_,h.unbounded.congr' (hr.mono fun _ e => congrArg Complex.re e),
    sector_eventually_analytic_congr h.analytic hf,h.maps_sector.congr' hf,C,hC,?_⟩
  · filter_upwards [h.positive,hr] with t ht he
    rwa [←he]
  · filter_upwards [hm,hf,tendsto_norm_sectorInfinity.eventually hr] with z hm he hr
    rwa [he,hr] at hm

lemma lowerSectorData_hasSectorCharts {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hKd : ∀ b : ℂ → ℂ,b∈K → deriv b∈K)
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K)
    (hcharts : LowerSectorCharts K) : HasSectorCharts K := by
  intro H hH hHr hHt hfast
  obtain ⟨y,I,hyi,_⟩ := hH.scalar_chart hK hKd hconj hcharts hH hHr hHr hHt hHt
    (Asymptotics.isBigO_refl _ _) hfast
  refine ⟨y,I,hyi,?_⟩
  intro F hF hFr hFt hO
  obtain ⟨v,J,hvj,hFv,hs⟩ := hF.scalar_chart hK hKd hconj hcharts hH hFr hHr hFt hHt hO hfast
  have he := sector_inverse_unique hH.choose_spec.choose_spec.1.eventually_analytic
    (hHr.mono fun _ h => h.1) hHt (hvj.analytic_left.mono fun _ h => h.1)
    (hyi.analytic_left.mono fun _ h => h.1) hvj.right hyi.right
  refine ⟨hFv.congr_inverse he,fun hsmall => ?_⟩
  exact (hs hsmall).congr' (he.mono fun _ h => congrArg (fun w => (F w).re) h) Filter.EventuallyEq.rfl

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ExpBound.comp_slow {F y : ℂ → ℂ} {a : ℝ} (hF : ExpBound a F)
    (hy : Tendsto y sectorInfinity sectorInfinity)
    (hs : (fun z => (y z).re) =o[sectorInfinity] Complex.re) :
    SectorSlow (fun z => F (y z)) := by
  intro ε hε
  obtain ⟨C,hC,hb⟩ := hF.exists_pos
  apply Asymptotics.IsBigO.of_bound C
  have hh := (hs.def (show 0 < ε/(|a|+1) by positivity))
  filter_upwards [hy.eventually hb.bound,hh,tendsto_re_sectorInfinity.eventually (eventually_gt_atTop 0)] with z h hz hpos
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at h ⊢
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have ha : a*(y z).re ≤ |a| * |(y z).re| := le_trans (le_abs_self _) (by rw [abs_mul])
  have hz' : |(y z).re| ≤ ε/(|a|+1)*z.re := by simpa [Real.norm_eq_abs,abs_of_pos hpos] using hz
  have hden : 0 < |a| + 1 := by positivity
  have hh : |a| * (ε/(|a|+1)) ≤ ε := by
    have hd : |a|/(|a|+1) ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
    calc
      |a| * (ε/(|a|+1)) = ε*(|a|/(|a|+1)) := by ring
      _ ≤ ε*1 := mul_le_mul_of_nonneg_left hd hε.le
      _ = ε := mul_one _
  calc
    a*(y z).re ≤ |a| * |(y z).re| := ha
    _ ≤ |a| * (ε/(|a|+1)*z.re) := mul_le_mul_of_nonneg_left hz' (abs_nonneg a)
    _ ≤ ε*z.re := by nlinarith

lemma ExpansionOver.expBound_some {K : Set (ℂ → ℂ)} {F : ℂ → ℂ}
    (hF : ExpansionOver K F) : ∃ a : ℝ,ExpBound a F := by
  obtain ⟨E,b,hF,hb⟩ := hF
  obtain ⟨A,hA⟩ := hF.bounded_above
  exact ⟨A+1,hF.expBound hA⟩

lemma ExpansionOver.zero_or_ne {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    {F : ℂ → ℂ} (hF : ExpansionOver K F) :
    (∀ᶠ z in sectorInfinity,F z=0) ∨ (∀ᶠ z in sectorInfinity,F z≠0) := by
  classical
  obtain ⟨E,b,hF,hb⟩ := hF
  have ht := hF.trim_zero (fun β hβ => hK.analytic (hb β hβ))
  rcases (nonzeroRaySupport E b).eq_empty_or_nonempty with he | he
  · rw [he] at ht
    obtain ⟨ω,R,hω,ha⟩ := hF.eventually_analytic
    exact Or.inl (sector_zero_of_ray_zero hω ha ht.empty)
  · obtain ⟨β,hβ,hmax⟩ := exists_greatest_of_finite_above ht.finite_above he
    have hbne : ∀ᶠ z in sectorInfinity,b β z≠0 := by
      rcases hK.zero_or_ne (hb β hβ.1) with hz | hn
      · exact False.elim (hβ.2 (tendsto_real_sectorInfinity.eventually hz))
      · exact hn
    exact Or.inr (ht.eventually_ne_of_leading hβ hmax hbne (hK.slow (hK.inv_mem (hb β hβ.1))))

 
def TransportedFirstField (y : ℂ → ℂ) : Set (ℂ → ℂ) :=
  {b | ∃ F : ℂ → ℂ,ExpansionOver PuiseuxSector F ∧ b =ᶠ[sectorInfinity] fun z => F (y z)}

lemma transported_first_lowerSectorData {y : ℂ → ℂ}
    (hya : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z)
    (hyt : Tendsto y sectorInfinity sectorInfinity)
    (hys : (fun z => (y z).re) =o[sectorInfinity] Complex.re) :
    LowerSectorData (TransportedFirstField y) := by
  constructor
  · intro c
    exact ⟨fun _ => c,ExpansionOver.const puiseux_lowerSectorData c,EventuallyEq.rfl⟩
  · rintro f g ⟨F,hF,he⟩ ⟨G,hG,he'⟩
    exact ⟨fun z => F z+G z,hF.add puiseux_lowerSectorData hG,he.add he'⟩
  · rintro f ⟨F,hF,he⟩
    exact ⟨fun z => -F z,hF.neg puiseux_lowerSectorData,he.neg⟩
  · rintro f g ⟨F,hF,he⟩ ⟨G,hG,he'⟩
    exact ⟨fun z => F z*G z,hF.mul puiseux_lowerSectorData hG,he.mul he'⟩
  · rintro f ⟨F,hF,he⟩
    exact ⟨fun z => (F z)⁻¹,hF.inv puiseux_lowerSectorData,he.inv⟩
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
    rcases hF.zero_or_ne puiseux_lowerSectorData with hz | hn
    · exact Or.inl (he.trans (hyt.eventually hz))
    · exact Or.inr ((he.and (hyt.eventually hn)).mono fun z h => by rw [h.1]; exact h.2)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma puiseux_variable : Puiseux (fun t : ℝ => (t:ℂ)) := by
  refine ⟨1,by norm_num,-1,fun _ => 1,analyticAt_const,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  simp [rootCoord,Real.rpow_neg_one]

lemma ExpansionOver.puiseux_mem {F : ℂ → ℂ} (hF : F∈PuiseuxSector) :
    ExpansionOver PuiseuxSector F := by
  refine ⟨{0},fun _ => F,?_,fun _ _ => hF⟩
  simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using
    SectorExpansion.single 0 hF.1 (puiseux_lowerSectorData.slow hF)

lemma ExpansionOver.lower_field_chart {H : ℂ → ℂ}
    (hH : ExpansionOver PuiseuxSector H)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re)) :
    ∃ y : ℂ → ℂ,
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z ∧ H (y z)=z) ∧
      (∀ᶠ t : ℝ in atTop,y (H (t:ℂ))=(t:ℂ)) ∧
      Tendsto y sectorInfinity sectorInfinity ∧
      LowerSectorData (TransportedFirstField y) := by
  have hid : ExpansionOver PuiseuxSector id :=
    ExpansionOver.puiseux_mem ⟨Eventually.of_forall fun _ => analyticAt_id,puiseux_variable⟩
  have hir : ∀ᶠ t : ℝ in atTop,(id (t:ℂ)).im=0 ∧ 0<(id (t:ℂ)).re := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact ⟨rfl,ht⟩
  have hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(id (t:ℂ)).re≤D*(H (t:ℂ)).re := by
    refine ⟨1,zero_lt_one,?_⟩
    filter_upwards [hfast.def zero_lt_one,hHr] with t ht hr
    simp only [id_eq,Complex.ofReal_re,one_mul]
    exact (le_abs_self t).trans (by simpa [Real.norm_eq_abs,abs_of_pos hr.2] using ht)
  obtain ⟨y,J,hya,hyr,hyt,hJt,hyray,hrest⟩ := hH.first_level_common_chart hHr hHt hfast
  have hs := (hrest id hid hir tendsto_id hO).2 hfast
  exact ⟨y,hya,hyr,hyt,transported_first_lowerSectorData (hya.mono fun _ h => h.1) hyt hs⟩

 

lemma transported_first_iff {X Y : ℝ → ℝ} {y : ℂ → ℂ}
    (hX : Puiseux (fun t => (X t:ℂ))) (hXt : Tendsto X atTop atTop)
    (hYt : Tendsto Y atTop atTop)
    (hYc : ∀ᶠ t : ℝ in atTop,ContinuousAt Y t)
    (hya : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z)
    (hyt : Tendsto y sectorInfinity sectorInfinity)
    (hyr : ∀ᶠ t : ℝ in atTop,y (Y t:ℂ)=(X t:ℂ))
    {b : ℂ → ℂ} (hba : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ b z) :
    b ∈ TransportedFirstField y ↔ ClockGerm (X :: []) (fun t => b (Y t:ℂ)) := by
  constructor
  · rintro ⟨F,hF,he⟩
    apply (firstClock_expansion_iff hX hXt).mpr
    refine ⟨F,hF,?_⟩
    filter_upwards [hYt.eventually (tendsto_real_sectorInfinity.eventually he),hyr] with t he hy
    simpa only [hy] using he
  · intro hb
    obtain ⟨F,hF,he⟩ := (firstClock_expansion_iff hX hXt).mp hb
    refine ⟨F,hF,?_⟩
    have hfa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => F (y w)) z := by
      filter_upwards [hya,hyt.eventually hF.choose_spec.choose_spec.1.eventually_analytic] with z hy hf
      exact hf.comp hy
    apply sector_analytic_eq_of_ray hba hfa
    apply eventually_of_comp_clock hYt hYc
    filter_upwards [he,hyr] with t he hy
    simpa only [hy] using he

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma finite_strict_gap (S : Finset ℝ) {β ε : ℝ} (hε : 0 < ε)
    (hS : ∀ γ∈S,β < γ) :
    ∃ δ : ℝ,0 < δ ∧ δ < ε ∧ ∀ γ∈S,β+δ < γ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨ε/2,by positivity,by linarith,by simp⟩
  | @insert γ S hγ ih =>
    obtain ⟨δ,hδ,hδε,hbound⟩ := ih (fun a ha => hS a (Finset.mem_insert_of_mem ha))
    have hg := hS γ (Finset.mem_insert_self _ _)
    refine ⟨min δ ((γ-β)/2),lt_min hδ (by linarith),
      (min_le_left _ _).trans_lt hδε,?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · have hh := min_le_right δ ((a-β)/2)
      linarith
    · have hmin := min_le_left δ ((γ-β)/2)
      have hh := hbound a ha
      linarith

theorem SectorExpansion.coefficient_slow {F : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hF : SectorExpansion F E b) {β : ℝ} (hβ : β∈E) : SectorSlow (b β) := by
  classical
  intro ε hε
  let S := (hF.finite_above β).toFinset.erase β
  obtain ⟨δ,hδ,hδε,hgap⟩ := finite_strict_gap S hε (fun γ hγ => by
    have hh := Finset.mem_erase.mp hγ
    have hge := ((hF.finite_above β).mem_toFinset.mp hh.2).2
    exact lt_of_le_of_ne hge (Ne.symm hh.1))
  have he : (hF.finite_above β).toFinset=insert β (hF.finite_above (β+δ)).toFinset := by
    ext γ
    simp only [Set.Finite.mem_toFinset,Set.mem_inter_iff,Set.mem_Ici,Finset.mem_insert]
    constructor
    · rintro ⟨hγ,hγβ⟩
      by_cases hh : γ=β
      · exact Or.inl hh
      · exact Or.inr ⟨hγ,(hgap γ (Finset.mem_erase.mpr ⟨hh,(hF.finite_above β).mem_toFinset.mpr ⟨hγ,hγβ⟩⟩)).le⟩
    · rintro (rfl | ⟨hγ,hγδ⟩)
      · exact ⟨hβ,le_rfl⟩
      · exact ⟨hγ,by linarith⟩
  have hn : β∉(hF.finite_above (β+δ)).toFinset := by
    intro hh
    have hg := ((hF.finite_above (β+δ)).mem_toFinset.mp hh).2
    change β+δ ≤ β at hg
    linarith
  obtain ⟨a,ha,hA⟩ := hF.expSmall_remainder (β+δ)
  obtain ⟨c,hc,hC⟩ := hF.expSmall_remainder β
  have hh := ((hA.mono (le_of_lt (by linarith : a < β+ε))).sub
    (hC.mono (le_of_lt (by linarith : c < β+ε)))).mul (ExpBound.cexp (-β))
  have hid : β+ε+-β=ε := by ring
  rw [hid] at hh
  apply hh.congr_left
  intro z
  rw [he,Finset.sum_insert hn]
  have hexp : Complex.exp ((β:ℂ)*z)*Complex.exp (((-β:ℝ):ℂ)*z)=1 := by
    rw [←Complex.exp_add]
    convert Complex.exp_zero using 1
    push_cast
    ring_nf
  calc
    ((F z-∑ a∈(hF.finite_above (β+δ)).toFinset,Complex.exp ((a:ℂ)*z)*b a z)-
      (F z-(Complex.exp ((β:ℂ)*z)*b β z+∑ a∈(hF.finite_above (β+δ)).toFinset,Complex.exp ((a:ℂ)*z)*b a z)))*
        Complex.exp (((-β:ℝ):ℂ)*z)=
      (Complex.exp ((β:ℂ)*z)*Complex.exp (((-β:ℝ):ℂ)*z))*b β z := by ring
    _ = b β z := by rw [hexp,one_mul]

end DegeneratingTrees.Clock
end

end OAI
