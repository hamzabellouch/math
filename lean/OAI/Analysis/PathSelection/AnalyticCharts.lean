import Mathlib
import OAI.Analysis.PathSelection.PositiveCharts

namespace OAI

/-! Analytic Puiseux charts, zero leading data and clock perturbation estimates. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma PositiveSectorControl.tendsto {f : ℝ → ℝ} (hf : PositiveSectorControl f) :
    ∃ G : ℂ → ℂ,(∀ᶠ z in sectorInfinity,AnalyticAt ℂ G z) ∧
      (fun t => (f t:ℂ)) =ᶠ[atTop] (fun t => G (t:ℂ)) ∧
      Tendsto G sectorInfinity sectorInfinity ∧
      (∀ᶠ z in sectorInfinity,|f ‖z‖|/4≤‖G z‖ ∧ ‖G z‖≤4*|f ‖z‖|) ∧
      ∀ ω S,AdmissibleAngularLoss ω →
        ∃ η R,AdmissibleAngularLoss η ∧
          (∀ z∈lossSector η R,G z∈lossSector ω S) ∧
          (f =o[atTop] id → ∀ ε : ℝ,0<ε → ∃ A : ℝ,
            ∀ z∈lossSector η A,|(G z).re|≤ε*z.re) := by
  obtain ⟨G,R,hGa,he,hm,hmap⟩ := hf
  refine ⟨G,sector_halfplane_analytic hGa,he,?_,?_,?_⟩
  · apply Filter.tendsto_def.mpr
    intro U hU
    obtain ⟨ω,S,hω,hU⟩ := hU
    obtain ⟨η,T,hη,_,hT,_⟩ := hmap ω S hω
    exact ⟨η,T,hη,fun z hz => hU _ (hT z hz)⟩
  · exact (tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop R)).mono hm
  · intro ω S hω
    obtain ⟨η,T,hη,_,hT,hsmall⟩ := hmap ω S hω
    exact ⟨η,T,hη,hT,hsmall⟩

 

theorem PuiseuxSector.analytic_change_clock {H : ℂ → ℂ}
    (hH : H∈PuiseuxSector)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re)) :
    ∃ (I : ℝ → ℝ) (x : ℂ → ℂ),Puiseux (fun t => (I t:ℂ)) ∧
      Tendsto I atTop atTop ∧ I =o[atTop] id ∧
      (∀ᶠ z in sectorInfinity,AnalyticAt ℂ x z ∧ H (x z)=z) ∧
      Tendsto x sectorInfinity sectorInfinity ∧
      (∀ᶠ t : ℝ in atTop,x (t:ℂ)=(I t:ℂ) ∧ H (I t:ℂ)=(t:ℂ)) ∧
      (∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ)) ∧
      (∀ᶠ z in sectorInfinity,I ‖z‖/4≤‖x z‖ ∧ ‖x z‖≤4*I ‖z‖) ∧
      ∀ F : ℂ → ℂ,F∈PuiseuxSector →
        (∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0) →
        Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop →
        (fun t : ℝ => (F (t:ℂ)).re) =O[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
        (∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun w => F (x w)) z) ∧
        Tendsto (fun w => F (x w)) sectorInfinity sectorInfinity ∧
        (∀ᶠ z in sectorInfinity,‖F (x (‖z‖:ℂ))‖/4≤‖F (x z)‖ ∧
          ‖F (x z)‖≤4*‖F (x (‖z‖:ℂ))‖) ∧
        ∀ ω S,AdmissibleAngularLoss ω →
          ∃ η R,AdmissibleAngularLoss η ∧
            (∀ z∈lossSector η R,F (x z)∈lossSector ω S) ∧
            ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
              ∀ ε : ℝ,0<ε → ∃ A : ℝ,∀ z∈lossSector η A,|(F (x z)).re|≤ε*z.re) := by
  obtain ⟨I,hI,hIt,hl,hr,hIo,hIc,hfamily⟩ := (PuiseuxSector.real_puiseux hH hHr).change_clock hHt hfast
  obtain ⟨x,hxa,he,hxt,hm,hmap⟩ := hIc.tendsto
  have hxr : ∀ᶠ t : ℝ in atTop,x (t:ℂ)=(I t:ℂ) := he.symm
  have hHreal : ∀ᶠ t : ℝ in atTop,H (t:ℂ)=((H (t:ℂ)).re:ℂ) :=
    hHr.mono fun _ ht => Complex.ext rfl (by simpa using ht)
  have hleft : ∀ᶠ t : ℝ in atTop,H (I t:ℂ)=(t:ℂ) := by
    filter_upwards [hl,hIt.eventually hHreal] with t ht hre
    rw [hre,ht]
  have hHa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => H (x z)) z := by
    filter_upwards [hxa,hxt.eventually hH.1] with z hx hH
    exact hH.comp hx
  have hleftC : (fun z => H (x z)) =ᶠ[sectorInfinity] id :=
    sector_analytic_eq_of_ray hHa (Eventually.of_forall fun _ => analyticAt_id)
      (by filter_upwards [hxr,hleft] with t hx hl; simpa [hx] using hl)
  have hright : ∀ᶠ t : ℝ in atTop,x (H (t:ℂ))=(t:ℂ) := by
    filter_upwards [hHreal,hr,hHt.eventually hxr] with t hre hr hx
    rw [hre,hx,hr]
  have hipos := hIt.eventually (eventually_gt_atTop (0:ℝ))
  refine ⟨I,x,hI,hIt,hIo,hxa.and hleftC,hxt,hxr.and hleft,hright,?_,?_⟩
  · filter_upwards [hm,tendsto_norm_sectorInfinity.eventually hipos] with z hm hp
    simpa only [abs_of_pos hp] using hm
  · intro F hF hFr hFt hFO
    obtain ⟨hFc,hFo⟩ := hfamily _ (PuiseuxSector.real_puiseux hF hFr) hFt hFO
    obtain ⟨G,hGa,hGe,hGt,hGm,hGmap⟩ := hFc.tendsto
    have hFa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ (fun z => F (x z)) z := by
      filter_upwards [hxa,hxt.eventually hF.1] with z hx hf
      exact hf.comp hx
    have hray : ∀ᶠ t : ℝ in atTop,F (x (t:ℂ))=G (t:ℂ) := by
      filter_upwards [hxr,hGe,hIt.eventually hFr] with t hx hg hr
      rw [hx,←hg]
      exact Complex.ext rfl (by simpa using hr)
    have heq := sector_analytic_eq_of_ray hFa hGa hray
    refine ⟨hFa,hGt.congr' heq.symm,?_,?_⟩
    · filter_upwards [hGm,heq,tendsto_norm_sectorInfinity.eventually hray,
        tendsto_norm_sectorInfinity.eventually hGe] with z hm he hr hg
      rw [he,hr,←hg,Complex.norm_real,Real.norm_eq_abs]
      exact hm
    · intro ω S hω
      obtain ⟨η,R,hη,hmap,hsmall⟩ := hGmap ω S hω
      obtain ⟨κ,K,hκ,hκe⟩ := heq
      refine ⟨fun r => max (η r) (κ r),max R K,hη.max hκ,?_,?_⟩
      · intro z hz
        have hηz : z∈lossSector η R := ⟨(le_max_left _ _).trans_lt hz.1,
          hz.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩
        have hκz : z∈lossSector κ K := ⟨(le_max_right _ _).trans_lt hz.1,
          hz.2.trans_le (sub_le_sub_left (le_max_right _ _) _)⟩
        have he : F (x z)=G z := hκe z hκz
        rw [he]
        exact hmap z hηz
      · intro ho ε hε
        obtain ⟨A,hA⟩ := hsmall (hFo ho) ε hε
        refine ⟨max A K,fun z hz => ?_⟩
        have hηz : z∈lossSector η A := ⟨(le_max_left _ _).trans_lt hz.1,
          hz.2.trans_le (sub_le_sub_left (le_max_left _ _) _)⟩
        have hκz : z∈lossSector κ K := ⟨(le_max_right _ _).trans_lt hz.1,
          hz.2.trans_le (sub_le_sub_left (le_max_right _ _) _)⟩
        have he : F (x z)=G z := hκe z hκz
        rw [he]
        exact hA z hηz

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma real_equivalent_of_relative {F g : ℂ → ℂ}
    (hF : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0)
    (hg : ∀ᶠ t : ℝ in atTop,(g (t:ℂ)).im=0 ∧ 0<(g (t:ℂ)).re)
    (he : ExpSmall 0 (fun z => F z/g z-1)) :
    (fun t : ℝ => (F (t:ℂ)).re) ~[atTop] (fun t : ℝ => (g (t:ℂ)).re) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one (hg.mono fun _ h => h.2.ne')).mpr
  have ht : Tendsto (fun z => F z/g z) sectorInfinity (𝓝 1) := by
    simpa only [sub_add_cancel,zero_add] using he.tendsto_zero.add_const 1
  have hr := (Complex.continuous_re.tendsto 1).comp (ht.comp tendsto_real_sectorInfinity)
  apply hr.congr'
  filter_upwards [hF,hg] with t hf hg
  have ef : F (t:ℂ)=((F (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hf)
  have eg : g (t:ℂ)=((g (t:ℂ)).re:ℂ) := Complex.ext rfl (by simpa using hg.1)
  change (F (t:ℂ)/g (t:ℂ)).re=(F (t:ℂ)).re/(g (t:ℂ)).re
  rw [ef,eg,←Complex.ofReal_div,Complex.ofReal_re]
  rfl

lemma Puiseux.log_littleO_unbounded {I : ℝ → ℝ}
    (hI : Puiseux (fun t => (I t:ℂ))) (hIt : Tendsto I atTop atTop) :
    Real.log =o[atTop] I := by
  obtain ⟨q,a,C,K,R,G,hq,ha,hC,hK,hGa,he,herr⟩ := hI.positive_sector hIt
  have hn := power_model_norm ha hC herr
  have hb : (fun t : ℝ => t^(q:ℝ)) =O[atTop] I := by
    apply Asymptotics.IsBigO.of_bound (2/C)
    filter_upwards [hn,he] with t ht he
    have hh := (ht.2 (t:ℂ) (Complex.norm_of_nonneg ht.1.le)).1
    simp only [←he,Complex.norm_real,Real.norm_eq_abs] at hh
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos ht.1 _),Real.norm_eq_abs]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hC).mpr
    nlinarith
  exact (isLittleO_log_rpow_atTop hq).trans_isBigO hb

lemma ExpSmall.common_sector_bound {E F : ℂ → ℂ} (hE : ExpSmall 0 E) (hF : ExpSmall 0 F) :
    ∃ ε C : ℝ,0<ε ∧ 0≤C ∧ ∀ᶠ z in sectorInfinity,
      ‖E z‖≤C*Real.exp (-ε*z.re) ∧ ‖F z‖≤C*Real.exp (-ε*z.re) := by
  obtain ⟨a,ha,hEa⟩ := hE
  obtain ⟨b,hb,hFb⟩ := hF
  obtain ⟨A,hA,hEA⟩ := hEa.exists_pos
  obtain ⟨B,hB,hFB⟩ := hFb.exists_pos
  refine ⟨-max a b,A+B,by have := max_lt ha hb; linarith,by positivity,?_⟩
  filter_upwards [hEA.bound,hFB.bound,
    show ∀ᶠ z in sectorInfinity,0<z.re from SectorEventually.realpart_pos] with z he hf hz
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at he hf
  simp only [neg_neg]
  have he' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left a b) hz.le)
  have hf' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right a b) hz.le)
  constructor
  · exact he.trans ((mul_le_mul_of_nonneg_left he' hA.le).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le))
  · exact hf.trans ((mul_le_mul_of_nonneg_left hf' hB.le).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le))

 

theorem ExpansionOver.zero_leading_data {F H : ℂ → ℂ}
    (hF : ExpansionOver PuiseuxSector F) (hH : ExpansionOver PuiseuxSector H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re))
    (htop : Tendsto (fun z => deriv H z/H z) sectorInfinity (𝓝 0)) :
    ∃ g h : ℂ → ℂ,g∈PuiseuxSector ∧ h∈PuiseuxSector ∧
      (∀ᶠ z in sectorInfinity,g z≠0 ∧ h z≠0) ∧
      (∀ᶠ t : ℝ in atTop,(g (t:ℂ)).im=0 ∧ 0<(g (t:ℂ)).re) ∧
      (∀ᶠ t : ℝ in atTop,(h (t:ℂ)).im=0 ∧ 0<(h (t:ℂ)).re) ∧
      Tendsto (fun t : ℝ => (g (t:ℂ)).re) atTop atTop ∧
      Tendsto (fun t : ℝ => (h (t:ℂ)).re) atTop atTop ∧
      id =o[atTop] (fun t : ℝ => (h (t:ℂ)).re) ∧
      (fun t : ℝ => (g (t:ℂ)).re) =O[atTop] (fun t : ℝ => (h (t:ℂ)).re) ∧
      ExpSmall 0 (fun z => F z/g z-1) ∧ ExpSmall 0 (fun z => H z/h z-1) ∧
      ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
        (fun t : ℝ => (g (t:ℂ)).re) =o[atTop] (fun t : ℝ => (h (t:ℂ)).re)) := by
  obtain ⟨a,ha,g,hg,hg0,hgr,hFe,hFd⟩ := hF.puiseux_positive_leading hFr hFt
  obtain ⟨b,hb,h,hh,hh0,hhr,hHe,hHd⟩ := hH.puiseux_positive_leading hHr hHt
  have hb0 : b=0 := Complex.ofReal_eq_zero.mp (tendsto_nhds_unique hHd htop)
  subst b
  have hFa := hF.choose_spec.choose_spec.1.eventually_analytic
  have hHa := hH.choose_spec.choose_spec.1.eventually_analytic
  have hab : a≤0 := unbounded_log_exponent_order (le_refl 0)
    (tendsto_real_sectorInfinity.eventually hFa) (tendsto_real_sectorInfinity.eventually hHa)
    hFr hHr hFt (hFd.comp tendsto_real_sectorInfinity) (hHd.comp tendsto_real_sectorInfinity) hO
  have ha0 := le_antisymm hab ha
  subst a
  have heF : ExpSmall 0 (fun z => F z/g z-1) := by simpa [div_eq_mul_inv,mul_comm] using hFe
  have heH : ExpSmall 0 (fun z => H z/h z-1) := by simpa [div_eq_mul_inv,mul_comm] using hHe
  have eqF := real_equivalent_of_relative (hFr.mono fun _ h => h.1) hgr heF
  have eqH := real_equivalent_of_relative (hHr.mono fun _ h => h.1) hhr heH
  have hbO : (fun t : ℝ => (F (t:ℂ)).re) =O[atTop] (fun t : ℝ => (H (t:ℂ)).re) := by
    obtain ⟨D,hD,hO⟩ := hO
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [hO,hFr,hHr] with t ht hf hh
    simpa only [Real.norm_eq_abs,abs_of_pos hf.2,abs_of_pos hh.2] using ht
  refine ⟨g,h,hg,hh,hg0.and hh0,hgr,hhr,eqF.tendsto_atTop hFt,eqH.tendsto_atTop hHt,
    hfast.trans_isBigO eqH.isBigO,eqF.symm.isBigO.trans (hbO.trans eqH.isBigO),heF,heH,?_⟩
  intro hl
  exact (eqF.symm.isBigO.trans_isLittleO hl).trans_isBigO eqH.isBigO

end DegeneratingTrees.Clock

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

theorem ExpansionOver.zero_leading_strip_data {K : Set (ℂ → ℂ)} (hK : LowerSectorData K)
    (hconj : ∀ b : ℂ → ℂ,b∈K → (fun z => star (b (star z)))∈K) {F H : ℂ → ℂ}
    (hF : ExpansionOver K F) (hH : ExpansionOver K H)
    (hFr : ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).im=0 ∧ 0<(F (t:ℂ)).re)
    (hHr : ∀ᶠ t : ℝ in atTop,(H (t:ℂ)).im=0 ∧ 0<(H (t:ℂ)).re)
    (hFt : Tendsto (fun t : ℝ => (F (t:ℂ)).re) atTop atTop)
    (hHt : Tendsto (fun t : ℝ => (H (t:ℂ)).re) atTop atTop)
    (hO : ∃ D : ℝ,0<D ∧ ∀ᶠ t : ℝ in atTop,(F (t:ℂ)).re≤D*(H (t:ℂ)).re)
    (hfast : id =o[atTop] (fun t : ℝ => (H (t:ℂ)).re))
    (htop : Tendsto (fun z => deriv H z/H z) stripInfinity (𝓝 0)) :
    ∃ g h : ℂ → ℂ,g∈K ∧ h∈K ∧
      (∀ᶠ z in sectorInfinity,g z≠0 ∧ h z≠0) ∧
      (∀ᶠ t : ℝ in atTop,(g (t:ℂ)).im=0 ∧ 0<(g (t:ℂ)).re) ∧
      (∀ᶠ t : ℝ in atTop,(h (t:ℂ)).im=0 ∧ 0<(h (t:ℂ)).re) ∧
      Tendsto (fun t : ℝ => (g (t:ℂ)).re) atTop atTop ∧
      Tendsto (fun t : ℝ => (h (t:ℂ)).re) atTop atTop ∧
      id =o[atTop] (fun t : ℝ => (h (t:ℂ)).re) ∧
      (fun t : ℝ => (g (t:ℂ)).re) =O[atTop] (fun t : ℝ => (h (t:ℂ)).re) ∧
      ExpSmall 0 (fun z => F z/g z-1) ∧ ExpSmall 0 (fun z => H z/h z-1) ∧
      ((fun t : ℝ => (F (t:ℂ)).re) =o[atTop] (fun t : ℝ => (H (t:ℂ)).re) →
        (fun t : ℝ => (g (t:ℂ)).re) =o[atTop] (fun t : ℝ => (h (t:ℂ)).re)) := by
  obtain ⟨a,ha,g,hg,hg0,hgr,hFe,hFd⟩ := hF.positive_leading_strip hK hconj hFr hFt
  obtain ⟨b,hb,h,hh,hh0,hhr,hHe,hHd⟩ := hH.positive_leading_strip hK hconj hHr hHt
  have hb0 : b=0 := Complex.ofReal_eq_zero.mp (tendsto_nhds_unique hHd htop)
  subst b
  have hFa := hF.choose_spec.choose_spec.1.eventually_analytic
  have hHa := hH.choose_spec.choose_spec.1.eventually_analytic
  have hab : a≤0 := unbounded_log_exponent_order (le_refl 0)
    (tendsto_real_sectorInfinity.eventually hFa) (tendsto_real_sectorInfinity.eventually hHa)
    hFr hHr hFt (hFd.comp tendsto_real_stripInfinity) (hHd.comp tendsto_real_stripInfinity) hO
  have ha0 := le_antisymm hab ha
  subst a
  have heF : ExpSmall 0 (fun z => F z/g z-1) := by simpa [div_eq_mul_inv,mul_comm] using hFe
  have heH : ExpSmall 0 (fun z => H z/h z-1) := by simpa [div_eq_mul_inv,mul_comm] using hHe
  have eqF := real_equivalent_of_relative (hFr.mono fun _ h => h.1) hgr heF
  have eqH := real_equivalent_of_relative (hHr.mono fun _ h => h.1) hhr heH
  have hbO : (fun t : ℝ => (F (t:ℂ)).re) =O[atTop] (fun t : ℝ => (H (t:ℂ)).re) := by
    obtain ⟨D,hD,hO⟩ := hO
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [hO,hFr,hHr] with t ht hf hh
    simpa only [Real.norm_eq_abs,abs_of_pos hf.2,abs_of_pos hh.2] using ht
  refine ⟨g,h,hg,hh,hg0.and hh0,hgr,hhr,eqF.tendsto_atTop hFt,eqH.tendsto_atTop hHt,
    hfast.trans_isBigO eqH.isBigO,eqF.symm.isBigO.trans (hbO.trans eqH.isBigO),heF,heH,?_⟩
  intro hl
  exact (eqF.symm.isBigO.trans_isLittleO hl).trans_isBigO eqH.isBigO

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
open scoped NNReal
namespace DegeneratingTrees.Clock

 

theorem analytic_perturbative_inverse {f : ℂ → ℂ} {S V : Set ℂ}
    (hV : IsOpen V)
    (r : ℂ → ℝ) (hr : ContinuousOn r V) (hrpos : ∀ w ∈ V, 0 < r w)
    (hdisc : ∀ w ∈ V, closedBall w (r w) ⊆ S)
    (hf : AnalyticOnNhd ℂ f S)
    (hder : ∀ w ∈ V, ∀ z ∈ ball w (r w), ‖deriv f z-1‖ ≤ (1/2:ℝ))
    (hsmall : ∀ w ∈ V, ‖f w-w‖ ≤ r w/4) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g V ∧
      (∀ w ∈ V, g w ∈ S ∧ f (g w) = w ∧ ‖g w-w‖ ≤ 2*‖f w-w‖) ∧
      (∀ w ∈ V, ∀ z ∈ ball w (r w), f z = w → g w = z) := by
  classical
  have hlocal (w : ℂ) (hw : w ∈ V) := analytic_near_identity_inverse
    (f := f) (s := ball w (r w)) (c := (1/2:ℝ≥0)) isOpen_ball
    (convex_ball _ _) (by norm_num) (hf.mono (ball_subset_closedBall.trans (hdisc w hw)))
    (by simpa using hder w hw)
  have hex (w : ℂ) (hw : w ∈ V) : ∃ z : ℂ,
      z ∈ ball w (r w) ∧ f z = w ∧ ‖z-w‖ ≤ 2*‖f w-w‖ := by
    obtain ⟨g,hga,hgf,hfg,hmetric,hball⟩ := hlocal w hw
    have hwball : w ∈ ball w (r w) := mem_ball_self (hrpos w hw)
    have hhalf : closedBall w (r w/2) ⊆ ball w (r w) :=
      closedBall_subset_ball (by linarith [hrpos w hw])
    have himage : w ∈ f '' ball w (r w) := by
      apply hball w (r w/2) (by linarith [hrpos w hw]) hhalf
      rw [mem_closedBall_iff_norm, norm_sub_rev]
      convert hsmall w hw using 1
      norm_num
      ring
    refine ⟨g w,(hfg w himage).1,(hfg w himage).2,?_⟩
    have hm := hmetric (g w) (hfg w himage).1 w hwball
    rw [(hfg w himage).2,norm_sub_rev w (f w)] at hm
    norm_num at hm
    linarith
  choose a ha using hex
  let g : ℂ → ℂ := fun w => if hw : w ∈ V then a w hw else 0
  have hg (w : ℂ) (hw : w ∈ V) :
      g w ∈ ball w (r w) ∧ f (g w) = w ∧ ‖g w-w‖ ≤ 2*‖f w-w‖ := by
    simpa only [g,dite_eq_left hw] using ha w hw
  have hgsmall (w : ℂ) (hw : w ∈ V) : ‖g w-w‖ ≤ r w/2 := by
    have := (hg w hw).2.2
    linarith [hsmall w hw]
  have huniq (w : ℂ) (hw : w ∈ V) (z : ℂ) (hz : z ∈ ball w (r w))
      (he : f z = w) : g w = z := by
    obtain ⟨a,ha,haf,hfa,hm,hball⟩ := hlocal w hw
    have h := hm (g w) (hg w hw).1 z hz
    rw [(hg w hw).2.1,he,sub_self,norm_zero] at h
    have hn : ‖g w-z‖ = 0 := by norm_num at h; nlinarith [norm_nonneg (g w-z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  refine ⟨g,?_,fun w hw => ⟨hdisc w hw (ball_subset_closedBall (hg w hw).1),
    (hg w hw).2⟩,huniq⟩
  intro w hw
  obtain ⟨a,ha,haf,hfa,hm,hball⟩ := hlocal w hw
  have hwimage : w ∈ f '' ball w (r w) := ⟨g w,(hg w hw).1,(hg w hw).2.1⟩
  have hann := ha w hwimage
  have hnear : ∀ᶠ v in 𝓝 w, v ∈ V ∧ g v ∈ ball w (r w) := by
    have hrc : ContinuousAt r w := (hr w hw).continuousAt (hV.mem_nhds hw)
    have hb : ∀ᶠ v in 𝓝 w, r v/2 + ‖v-w‖ < r w :=
      ((hrc.div_const 2).add (continuousAt_id.sub continuousAt_const).norm).eventually
        (gt_mem_nhds (by simpa using (show r w/2 < r w by linarith [hrpos w hw])))
    filter_upwards [hV.mem_nhds hw,hb] with v hv hbound
    refine ⟨hv,mem_ball_iff_norm.mpr ?_⟩
    calc ‖g v-w‖ ≤ ‖g v-v‖+‖v-w‖ := by simpa only [dist_eq_norm] using dist_triangle (g v) v w
      _ ≤ r v/2 + ‖v-w‖ := add_le_add (hgsmall v hv) le_rfl
      _ < r w := hbound
  apply hann.congr
  filter_upwards [hnear] with v hv
  calc a v = a (f (g v)) := congrArg a (hg v hv.1).2.1.symm
    _ = g v := haf (g v) hv.2

end DegeneratingTrees.Clock

 

 

 

open Set Complex Metric
namespace DegeneratingTrees.Clock

lemma closedBall_inside_double {w z : ℂ} {r : ℝ} (hz : z∈closedBall w r) :
    closedBall z r ⊆ closedBall w (2*r) := by
  intro u hu
  rw [mem_closedBall] at *
  exact (dist_triangle u z w).trans (by linarith)

lemma cauchy_deriv_inner_disc {f : ℂ → ℂ} {w : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall w (2*r)))
    (hM : ∀ z∈closedBall w (2*r),‖f z‖ ≤ M) :
    ∀ z∈closedBall w r,‖deriv f z‖ ≤ M/r := by
  intro z hz
  have hs := closedBall_inside_double hz
  have hd := hf.differentiableOn.diffContOnCl_ball hs
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd
    (fun u hu => hM _ (hs (sphere_subset_closedBall hu)))

lemma cauchy_increment_inner_disc {f : ℂ → ℂ} {w u v : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall w (2*r)))
    (hM : ∀ z∈closedBall w (2*r),‖f z‖ ≤ M)
    (hu : u∈closedBall w r) (hv : v∈closedBall w r) :
    ‖f v-f u‖ ≤ M/r*‖v-u‖ := by
  have hs : closedBall w r ⊆ closedBall w (2*r) := closedBall_subset_closedBall (by linarith)
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf z (hs hz)).differentiableAt)
    (cauchy_deriv_inner_disc hr hf hM) (convex_closedBall w r) hu hv

 

theorem analytic_inverse_of_disc_error {f : ℂ → ℂ} {S V : Set ℂ}
    (hV : IsOpen V) (r : ℂ → ℝ) (hr : ContinuousOn r V)
    (hrpos : ∀ w∈V,0 < r w)
    (hdisc : ∀ w∈V,closedBall w (2*r w) ⊆ S)
    (hf : AnalyticOnNhd ℂ f S)
    (herr : ∀ w∈V,∀ z∈closedBall w (2*r w),‖f z-z‖ ≤ r w/4) :
    ∃ g : ℂ → ℂ,AnalyticOnNhd ℂ g V ∧
      (∀ w∈V,g w∈S ∧ f (g w)=w ∧ ‖g w-w‖ ≤ 2*‖f w-w‖) ∧
      (∀ w∈V,∀ z∈ball w (r w),f z=w → g w=z) := by
  apply analytic_perturbative_inverse hV r hr hrpos
    (fun w hw => (closedBall_subset_closedBall (by linarith [hrpos w hw])).trans (hdisc w hw)) hf
  · intro w hw z hz
    let e : ℂ → ℂ := fun t => f t-t
    have he : AnalyticOnNhd ℂ e (closedBall w (2*r w)) :=
      (hf.mono (hdisc w hw)).sub analyticOnNhd_id
    have hd := cauchy_deriv_inner_disc (hrpos w hw) he (herr w hw)
      z (ball_subset_closedBall hz)
    have hzf : AnalyticAt ℂ f z := hf _ (hdisc w hw
      ((closedBall_subset_closedBall (by linarith [hrpos w hw])) (ball_subset_closedBall hz)))
    have hde : deriv e z=deriv f z-1 := by
      exact (hzf.differentiableAt.hasDerivAt.sub (hasDerivAt_id z)).deriv
    rw [hde] at hd
    have heq : r w/4/r w=(1/4:ℝ) := by field_simp [(hrpos w hw).ne']
    rw [heq] at hd
    linarith
  · intro w hw
    exact herr w hw w (mem_closedBall_self (by linarith [hrpos w hw]))

end DegeneratingTrees.Clock
end

end OAI
