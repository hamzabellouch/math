import Mathlib
import OAI.Analysis.PathSelection.RelativeErrors

namespace OAI

/-! First-level and lower-sector common clock charts. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

def SectorClockChart (F H : ℂ → ℂ) : Prop :=
  ∃ (y : ℂ → ℂ) (J : ℝ → ℝ),
    (∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z ∧ H (y z)=z) ∧
    (∀ᶠ t : ℝ in atTop,y (H (t:ℂ))=(t:ℂ)) ∧
    Tendsto y sectorInfinity sectorInfinity ∧ Tendsto J atTop atTop ∧
    (∀ᶠ t : ℝ in atTop,y (t:ℂ)=(J t:ℂ)) ∧
    (∀ᶠ t : ℝ in atTop,(F (y (t:ℂ))).im=0 ∧ 0<(F (y (t:ℂ))).re) ∧
    Tendsto (fun t : ℝ => (F (y (t:ℂ))).re) atTop atTop ∧
    (∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => F (y w)) z) ∧
    Tendsto (fun w => F (y w)) sectorInfinity sectorInfinity ∧
    (∀ᶠ z in sectorInfinity,‖F (y (‖z‖:ℂ))‖/16≤‖F (y z)‖ ∧
      ‖F (y z)‖≤16*‖F (y (‖z‖:ℂ))‖) ∧
    ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
      (fun z => (F (y z)).re) =o[sectorInfinity] Complex.re)

theorem ExpansionOver.first_zero_chart {F H : ℂ → ℂ}
    (hF : ExpansionOver PuiseuxSector F) (hH : ExpansionOver PuiseuxSector H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re))
    (htop : Tendsto (fun z => deriv H z/H z) sectorInfinity (𝓝 0)) :
    SectorClockChart F H := by
  obtain ⟨g,h,hg,hh,hne,hgr,hhr,hgt,hht,hhfast,hgo,hFe,hHe,hgo'⟩ :=
    hF.zero_leading_data hH hFr hHr hFt hHt hO hfast htop
  obtain ⟨I,x,hI,hIt,hIo,hxa,hxt,hxr,hxright,hxmod,hfamily⟩ :=
    PuiseuxSector.analytic_change_clock hh (hhr.mono fun _ h => h.1) hht hhfast
  obtain ⟨hGa,hGt,hGmod,hGmap⟩ := hfamily g hg (hgr.mono fun _ h => h.1) hgt hgo
  obtain ⟨ε,K,hε,hK,hErr⟩ := hFe.common_sector_bound hHe
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
    filter_upwards [hxa,hxt.eventually hFa,hxt.eventually hg.1,hxt.eventually hne] with z hx hf hg hn
    exact ((hf.comp hx.1).div (hg.comp hx.1) hn.1).sub analyticAt_const
  have hPe : ∀ᶠ z in sectorInfinity,‖P z-z‖≤K*‖z‖*Real.exp (-ε*(x z).re) := by
    filter_upwards [hxa,hxt.eventually hErr,hxt.eventually hne] with z hx he hn
    have heq : P z-z=z*(H (x z)/h (x z)-1) := by
      calc
        P z-z=H (x z)-h (x z) := by rw [hx.2]
        _=h (x z)*(H (x z)/h (x z)-1) := by field_simp [hn.2]
        _=z*(H (x z)/h (x z)-1) := by rw [hx.2]
    rw [heq,norm_mul]
    exact (mul_le_mul_of_nonneg_left he.2 (norm_nonneg z)).trans_eq (by ring)
  have hEe : ∀ᶠ z in sectorInfinity,‖E z‖≤K*Real.exp (-ε*(x z).re) :=
    (hxt.eventually hErr).mono fun _ he => he.1
  obtain ⟨D,hD,hDb⟩ := hgo.exists_pos
  have hGr : ∀ᶠ t : ℝ in atTop,‖G (t:ℂ)‖≤D*|t| := by
    filter_upwards [hxr,hIt.eventually hDb.bound,hIt.eventually hgr] with t hx hd hg
    have eh : (h (I t:ℂ)).re=t := congrArg Complex.re hx.2
    have eg : g (I t:ℂ)=((g (I t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hg.1)
    change ‖g (x (t:ℂ))‖≤D*|t|
    rw [hx.1,eg,Complex.norm_real,Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs,eh] using hd
  have hGu : ∀ᶠ z in sectorInfinity,‖G z‖≤(4*D)*‖z‖ := by
    filter_upwards [hGmod,tendsto_norm_sectorInfinity.eventually hGr] with z hm hr
    have hr' : ‖g (x (‖z‖:ℂ))‖≤D*‖z‖ := by simpa only [abs_of_nonneg (norm_nonneg _)] using hr
    exact hm.2.trans (by nlinarith)
  obtain ⟨v,J,hva,hvt,hJt,hvr,hvright,hfva,hfvt,hfvm,hfsep⟩ :=
    zero_exponent_chart hPa hPr (by norm_num : (1:ℝ)≤4) hK hε hIt
      (hI.log_littleO_unbounded hIt) hxmod hxt hPe hGa hEa hGt
      (show (0:ℝ)≤4*D by positivity) hGu (by norm_num : (0:ℝ)<4) hGmod hEe
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
  refine ⟨y,fun t => I (J t),?_,hyrt,hyt,hIJt,hyr,?_,?_,?_,hfvt.congr' hQt,?_,?_⟩
  · filter_upwards [hva,hvt.eventually hxa] with z hv hx
    exact ⟨hx.1.comp hv.1,hv.2⟩
  · filter_upwards [hyr,hIJt.eventually hFr] with t hy hf
    simpa only [hy,Function.comp_apply] using hf
  · exact (hFt.comp hIJt).congr' (hyr.mono fun t hy => by simp only [hy,Function.comp_apply])
  · filter_upwards [hva,hvt.eventually hxa,hyt.eventually hFa] with z hv hx hf
    exact hf.comp (hx.1.comp hv.1)
  · filter_upwards [hfvm,hQt,tendsto_norm_sectorInfinity.eventually (tendsto_real_sectorInfinity.eventually hQt)] with z hm he hr
    change ‖Q (‖z‖:ℂ)‖/(4*4)≤‖Q z‖ ∧ ‖Q z‖≤(4*4)*‖Q (‖z‖:ℂ)‖ at hm
    simpa only [he,hr,show (4:ℝ)*4=16 by norm_num] using hm
  · intro hsmall
    have hGs : (fun z => (G z).re) =o[sectorInfinity] Complex.re := by
      obtain ⟨η,R,hη,hm,hs⟩ := hGmap baseLoss 1 admissible_baseLoss
      apply Asymptotics.IsLittleO.of_bound
      intro δ hδ
      obtain ⟨A,hA⟩ := hs (hgo' hsmall) δ hδ
      have hb : ∀ᶠ z in sectorInfinity,|(G z).re|≤δ*z.re := ⟨η,A,hη,hA⟩
      filter_upwards [hb] with z hz
      simp only [Real.norm_eq_abs]
      exact hz.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hδ.le)
    exact (hfsep hGs).congr' (hQt.mono fun _ he => congrArg Complex.re he) Filter.EventuallyEq.rfl

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma real_quotient_tendsto_zero {F H : ℂ → ℂ}
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0)
    (ho : (fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re)) :
    Tendsto (fun t : ℝ => F (t:ℂ)/H (t:ℂ)) atTop (𝓝 0) := by
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp ho.tendsto_div_nhds_zero
  apply ht.congr'
  filter_upwards [hFr,hHr] with t hf hh
  have ef : F (t:ℂ)=((F (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hf)
  have eh : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hh)
  change (((F (t:ℂ)).re/(H (t:ℂ)).re:ℝ):ℂ)=F (t:ℂ)/H (t:ℂ)
  rw [Complex.ofReal_div]
  exact congrArg₂ (fun a b : ℂ => a/b) ef.symm eh.symm

lemma PositiveExponentialChart.sector {F H : ℂ → ℂ}
    (h : PositiveExponentialChart F H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0) :
    SectorClockChart F H := by
  obtain ⟨T,x,hT,hxa,hl,hr,hxt,hxr,hft,hfa,hmap⟩ := h
  have hJt : Tendsto (fun t : ℝ => (x (t:ℂ)).re) atTop atTop :=
    tendsto_re_stripInfinity.comp (hxt.comp tendsto_real_sectorInfinity)
  have hyd : ∀ᶠ z in sectorInfinity,0<z.re ∧ T<‖z‖ :=
    SectorEventually.realpart_pos.and (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop T))
  have hyr : ∀ᶠ t : ℝ in atTop,x (t:ℂ)=((x (t:ℂ)).re:ℂ) :=
    hxr.mono fun t ht => Complex.ext rfl (by simpa using ht.1)
  have hmapping : Tendsto (fun z => F (x z)) sectorInfinity sectorInfinity := by
    apply Filter.tendsto_def.mpr
    intro U hU
    obtain ⟨ω,S,hω,hU⟩ := hU
    obtain ⟨η,R,hη,hm,hn,hs⟩ := hmap ω S hω
    exact ⟨η,R,hη,fun z hz => hU _ (hm z hz)⟩
  obtain ⟨η,R,hη,hm,hn,hs⟩ := hmap baseLoss 1 admissible_baseLoss
  refine ⟨x,fun t : ℝ => (x (t:ℂ)).re,
    hyd.mono (fun z hz => ⟨hxa z hz,hl z hz.1 hz.2⟩),hr,
    hxt.mono_right stripInfinity_le_sectorInfinity,hJt,hyr,
    hxr.mono (fun _ ht => ht.2),hft,hfa,hmapping,?_,?_⟩
  · have hn' : ∀ᶠ z in sectorInfinity,(F (x (‖z‖:ℂ))).re/2≤‖F (x z)‖ ∧
        ‖F (x z)‖≤2*(F (x (‖z‖:ℂ))).re := ⟨η,R,hη,hn⟩
    filter_upwards [hn',tendsto_norm_sectorInfinity.eventually hxr] with z hn hr
    have eq : F (x (‖z‖:ℂ))=((F (x (‖z‖:ℂ))).re:ℂ) :=
      Complex.ext rfl (by simpa using hr.2.1)
    rw [eq,Complex.norm_of_nonneg hr.2.2.le]
    constructor <;> nlinarith
  · intro ho
    have ht := real_quotient_tendsto_zero hFr hHr ho
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    obtain ⟨A,hA⟩ := hs ht ε hε
    have hb : ∀ᶠ z in sectorInfinity,|(F (x z)).re|≤ε*z.re := ⟨η,A,hη,hA⟩
    filter_upwards [hb] with z hz
    simp only [Real.norm_eq_abs]
    exact hz.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hε.le)

 

theorem ExpansionOver.first_level_chart {F H : ℂ → ℂ}
    (hF : ExpansionOver PuiseuxSector F) (hH : ExpansionOver PuiseuxSector H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re)) :
    SectorClockChart F H := by
  obtain ⟨b,hb,g,hg,hg0,hgr,hHe,hHd⟩ := hH.puiseux_positive_leading hHr hHt
  rcases hb.eq_or_lt with hb | hb
  · have hzero : Tendsto (fun z => deriv H z/H z) sectorInfinity (𝓝 0) := by
      simpa only [←hb,Complex.ofReal_zero] using hHd
    exact hF.first_zero_chart hH hFr hHr hFt hHt hO hfast hzero
  · exact (hF.first_positive_chart hH hFr hHr hFt hHt hO ⟨b,hb,hHd⟩).sector
      (hFr.mono fun _ h => h.1) (hHr.mono fun _ h => h.1)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma sector_inverse_unique {H x y : ℂ → ℂ}
    (hHa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ H z)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hxa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ x z)
    (hya : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z)
    (hx : ∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ))
    (hy : ∀ᶠ t : ℝ in atTop,y (H (t:ℂ))=(t:ℂ)) :
    x =ᶠ[sectorInfinity] y := by
  have hc : ∀ᶠ t : ℝ in atTop,ContinuousAt (fun t : ℝ => (H (t:ℂ)).re) t := by
    filter_upwards [tendsto_real_sectorInfinity.eventually hHa] with t ht
    exact Complex.continuous_re.continuousAt.comp
      (ht.continuousAt.comp Complex.continuous_ofReal.continuousAt)
  apply sector_analytic_eq_of_ray hxa hya
  apply eventually_of_comp_clock hHt hc
  filter_upwards [hx,hy,hHr] with t hx hy hr
  have he : H (t:ℂ)=((H (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hr)
  change x ((H (t:ℂ)).re:ℂ)=y ((H (t:ℂ)).re:ℂ)
  rw [←he,hx,hy]

 

def ScalarChartAt (F y : ℂ → ℂ) : Prop :=
  (∀ᶠ t : ℝ in atTop,(F (y (t:ℂ))).im=0 ∧ 0<(F (y (t:ℂ))).re) ∧
  Tendsto (fun t : ℝ => (F (y (t:ℂ))).re) atTop atTop ∧
  (∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => F (y w)) z) ∧
  Tendsto (fun w => F (y w)) sectorInfinity sectorInfinity ∧
  (∀ᶠ z in sectorInfinity,‖F (y (‖z‖:ℂ))‖/16≤‖F (y z)‖ ∧
    ‖F (y z)‖≤16*‖F (y (‖z‖:ℂ))‖)

theorem ExpansionOver.first_level_common_chart {H : ℂ → ℂ}
    (hH : ExpansionOver PuiseuxSector H)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re)) :
    ∃ (y : ℂ → ℂ) (J : ℝ → ℝ),
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z ∧ H (y z)=z) ∧
      (∀ᶠ t : ℝ in atTop,y (H (t:ℂ))=(t:ℂ)) ∧
      Tendsto y sectorInfinity sectorInfinity ∧ Tendsto J atTop atTop ∧
      (∀ᶠ t : ℝ in atTop,y (t:ℂ)=(J t:ℂ)) ∧
      ∀ F : ℂ → ℂ,ExpansionOver PuiseuxSector F →
        (∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re) →
        Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop →
        (∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re) →
        ScalarChartAt F y ∧
        ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
          (fun z => (F (y z)).re) =o[sectorInfinity] Complex.re) := by
  have hself : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).re≤D*(H (t:ℂ)).re :=
    ⟨1,zero_lt_one,Eventually.of_forall fun _ => by simp⟩
  obtain ⟨y,J,hya,hyr,hyt,hJt,hyray,hyHr,hyHt,hyHa,hyHt',hyHm,hyHs⟩ :=
    hH.first_level_chart hH hHr hHr hHt hHt hself hfast
  refine ⟨y,J,hya,hyr,hyt,hJt,hyray,?_⟩
  intro F hF hFr hFt hO
  obtain ⟨v,I,hva,hvr,hvt,hIt,hvray,hFvr,hFvt,hFva,hFvt',hFvm,hFvs⟩ :=
    hF.first_level_chart hH hFr hHr hFt hHt hO hfast
  have hvy := sector_inverse_unique hH.choose_spec.choose_spec.1.eventually_analytic
    (hHr.mono fun _ h => h.1) hHt (hva.mono fun _ h => h.1) (hya.mono fun _ h => h.1) hvr hyr
  have he : (fun z => F (v z)) =ᶠ[sectorInfinity] (fun z => F (y z)) :=
    hvy.mono fun _ ht => congrArg F ht
  have her := tendsto_real_sectorInfinity.eventually he
  refine ⟨⟨?_,hFvt.congr' (her.mono fun _ ht => congrArg Complex.re ht),?_,hFvt'.congr' he,?_⟩,?_⟩
  · filter_upwards [her,hFvr] with t he hr
    rwa [←he]
  · filter_upwards [hya,hyt.eventually hF.choose_spec.choose_spec.1.eventually_analytic] with z hy hf
    exact hf.comp hy.1
  · filter_upwards [he,hFvm,tendsto_norm_sectorInfinity.eventually her] with z he hm hr
    rwa [he,hr] at hm
  · intro hs
    exact (hFvs hs).congr' (he.mono fun _ ht => congrArg Complex.re ht) Filter.EventuallyEq.rfl

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

structure SectorInverse (H y : ℂ → ℂ) (I : ℝ → ℝ) : Prop where
  analytic_left : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ y z ∧ H (y z)=z
  right : ∀ᶠ t : ℝ in atTop,y (H (t:ℂ))=(t:ℂ)
  maps_sector : Tendsto y sectorInfinity sectorInfinity
  ray_unbounded : Tendsto I atTop atTop
  real_ray : ∀ᶠ t : ℝ in atTop,y (t:ℂ)=(I t:ℂ)

structure ScalarSectorChart (F y : ℂ → ℂ) : Prop where
  positive : ∀ᶠ t : ℝ in atTop,(F (y (t:ℂ))).im=0 ∧ 0<(F (y (t:ℂ))).re
  unbounded : Tendsto (fun t : ℝ => (F (y (t:ℂ))).re) atTop atTop
  analytic : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => F (y w)) z
  maps_sector : Tendsto (fun w => F (y w)) sectorInfinity sectorInfinity
  radial : ∃ C : ℝ,0<C ∧ ∀ᶠ z in sectorInfinity,
    ‖F (y (‖z‖:ℂ))‖/C≤‖F (y z)‖ ∧ ‖F (y z)‖≤C*‖F (y (‖z‖:ℂ))‖

def HasSectorCharts (K : Set (ℂ → ℂ)) : Prop :=
  ∀ H : ℂ → ℂ,ExpansionOver K H →
    (∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re) →
    Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop →
    id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
    ∃ (y : ℂ → ℂ) (I : ℝ → ℝ),SectorInverse H y I ∧
      ∀ F : ℂ → ℂ,ExpansionOver K F →
        (∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re) →
        Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop →
        (fun t : ℝ => (F (t:ℂ)).re) =O[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
        ScalarSectorChart F y ∧
        ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
          (fun z => (F (y z)).re) =o[sectorInfinity] Complex.re)

lemma real_positive_bigO {F H : ℂ → ℂ}
    (hFr : ∀ᶠ t : ℝ in atTop,0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,0<(H (t:ℂ)).re)
    (hO : (fun t : ℝ => (F (t:ℂ)).re) =O[atTop] (fun t : ℝ => (H (t:ℂ)).re)) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re := by
  obtain ⟨D,hD,hDb⟩ := hO.exists_pos
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb.bound,hFr,hHr] with t h hf hh
  simpa only [Real.norm_eq_abs,abs_of_pos hf,abs_of_pos hh] using h

lemma puiseux_hasSectorCharts : HasSectorCharts PuiseuxSector := by
  intro H hH hr ht hfast
  obtain ⟨y,I,ha,hright,hmap,hIt,hreal,hfamily⟩ := hH.first_level_common_chart hr ht hfast
  refine ⟨y,I,⟨ha,hright,hmap,hIt,hreal⟩,?_⟩
  intro F hF hFr hFt hFO
  obtain ⟨⟨hpos,hunb,hana,hmap,hnorm⟩,hsmall⟩ := hfamily F hF hFr hFt
    (real_positive_bigO (hFr.mono fun _ h => h.2) (hr.mono fun _ h => h.2) hFO)
  exact ⟨⟨hpos,hunb,hana,hmap,16,by norm_num,hnorm⟩,hsmall⟩

end DegeneratingTrees.Clock

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

 

def LowerSectorCharts (K : Set (ℂ → ℂ)) : Prop :=
  ∀ H : ℂ → ℂ,H∈K →
    (∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re) →
    Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop →
    id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
    ∃ (y : ℂ → ℂ) (I : ℝ → ℝ),SectorInverse H y I ∧
      Real.log =o[atTop] I ∧
      (∃ C : ℝ,1≤C ∧ ∀ᶠ z in sectorInfinity,I ‖z‖/C≤‖y z‖ ∧ ‖y z‖≤C*I ‖z‖) ∧
      ∀ F : ℂ → ℂ,F∈K →
        (∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re) →
        Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop →
        (fun t : ℝ => (F (t:ℂ)).re) =O[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
        ScalarSectorChart F y ∧
        ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
          (fun z => (F (y z)).re) =o[sectorInfinity] Complex.re)

end DegeneratingTrees.Clock
end

end OAI
