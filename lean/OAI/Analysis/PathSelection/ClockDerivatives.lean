import Mathlib
import OAI.Analysis.PathSelection.RecursiveClocks

namespace OAI

/-! Differentiation and logarithmic derivatives of first clocks and Puiseux series. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma hasDerivAt_expTerm {b : ℂ → ℂ} {z : ℂ} (hb : AnalyticAt ℂ b z) (β : ℝ) :
    HasDerivAt (fun w : ℂ => Complex.exp ((β:ℂ)*w)*b w)
      (Complex.exp ((β:ℂ)*z)*((β:ℂ)*b z+deriv b z)) z := by
  convert (((Complex.hasDerivAt_exp ((β:ℂ)*z)).comp z
    ((hasDerivAt_id z).const_mul (β:ℂ))).mul hb.differentiableAt.hasDerivAt) using 1 <;> try rfl
  simp only [Function.comp_apply, mul_one]
  ring

lemma analyticAt_expTerm {b : ℂ → ℂ} {z : ℂ} (hb : AnalyticAt ℂ b z) (β : ℝ) :
    AnalyticAt ℂ (fun w : ℂ => Complex.exp ((β:ℂ)*w)*b w) z :=
  ((analyticAt_const.mul analyticAt_id).cexp).mul hb

 

theorem SectorExpansion.deriv {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (h : SectorExpansion f E b)
    (ha : ∀ β ∈ E, SectorEventually (fun z => AnalyticAt ℂ (b β) z)) :
    SectorExpansion (deriv f) E (fun β z => (β:ℂ)*b β z+deriv (b β) z) := by
  classical
  refine ⟨h.bounded_above,h.finite_above,?_⟩
  intro B
  obtain ⟨ω,R,ε,C,hω,hε,hC,hf,hrem⟩ := h.remainders B
  let S := (h.finite_above B).toFinset
  have hcoeff : SectorEventually (fun z => ∀ β ∈ S, AnalyticAt ℂ (b β) z) := by
    apply SectorEventually.finset_forall S SectorEventually.truth
    intro β hβ
    exact ha β ((h.finite_above B).mem_toFinset.mp hβ).1
  have horig : SectorEventually (fun z => z ∈ lossSector ω R) := ⟨ω,R,hω,fun _ hz => hz⟩
  obtain ⟨η,T,hη,hboth⟩ := hcoeff.and horig
  let g : ℂ → ℂ := fun z => f z-∑ β ∈ S,Complex.exp ((β:ℂ)*z)*b β z
  have hg : AnalyticOnNhd ℂ g (lossSector η T) := by
    intro z hz
    apply (hf z (hboth z hz).2).sub
    exact (S.analyticAt_fun_sum (fun β hβ => analyticAt_expTerm ((hboth z hz).1 β hβ) β))
  have hgb : ∀ z ∈ lossSector η T, ‖g z‖ ≤ C*Real.exp ((B-ε)*z.re) :=
    fun z hz => hrem z (hboth z hz).2
  obtain ⟨ν,U,hν,hTU,hgd,hgdb⟩ := sector_deriv_bound hη hg hC hgb
  have hnew : SectorEventually (fun z => z ∈ lossSector ν U) := ⟨ν,U,hν,fun _ hz => hz⟩
  have hold : SectorEventually (fun z => z ∈ lossSector η T) := ⟨η,T,hη,fun _ hz => hz⟩
  obtain ⟨ξ,V,hξ,hv⟩ := hnew.and hold
  refine ⟨ξ,V,ε,C*Real.exp |B-ε|,hξ,hε,mul_nonneg hC (Real.exp_pos _).le,?_,?_⟩
  · intro z hz
    exact (hf z (hboth z (hv z hz).2).2).deriv
  · intro z hz
    have hfa := hf z (hboth z (hv z hz).2).2
    have hba := (hboth z (hv z hz).2).1
    have hsum := HasDerivAt.fun_sum (u := S) (fun β hβ => hasDerivAt_expTerm (hba β hβ) β)
    have hder := (hfa.differentiableAt.hasDerivAt.sub hsum).deriv
    have hb := hgdb z (hv z hz).1
    change ‖_root_.deriv g z‖ ≤ _ at hb
    rw [show _root_.deriv g z = _root_.deriv f z - ∑ β ∈ S,
      Complex.exp ((β:ℂ)*z)*((β:ℂ)*b β z+_root_.deriv (b β) z) from hder] at hb
    exact hb

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma PuiseuxSector.deriv_mem {f : ℂ → ℂ} (hf : f∈PuiseuxSector) :
    deriv f∈PuiseuxSector := by
  refine ⟨hf.1.mono (fun _ h => h.deriv),?_⟩
  apply hf.2.deriv.congr
  filter_upwards [tendsto_real_sectorInfinity.eventually hf.1] with t ht
  exact ht.differentiableAt.hasDerivAt.comp_ofReal.deriv

lemma ExpansionOver.puiseux_deriv {F : ℂ → ℂ} (hF : ExpansionOver PuiseuxSector F) :
    ExpansionOver PuiseuxSector (deriv F) := by
  obtain ⟨E,b,hF,hb⟩ := hF
  refine ⟨E,fun β z => (β:ℂ)*b β z+deriv (b β) z,
    hF.deriv (fun β hβ => (hb β hβ).1),?_⟩
  intro β hβ
  exact puiseux_lowerSectorData.add_mem
    (puiseux_lowerSectorData.mul_mem (puiseux_lowerSectorData.const_mem (β:ℂ)) (hb β hβ))
    (PuiseuxSector.deriv_mem (hb β hβ))

lemma Puiseux.sector_representative {f : ℝ → ℂ} (hf : Puiseux f) :
    ∃ F : ℂ → ℂ,F∈PuiseuxSector ∧ f =ᶠ[atTop] fun t => F (t:ℂ) := by
  by_cases hz : f =ᶠ[atTop] fun _ => 0
  · exact ⟨fun _ => 0,puiseux_lowerSectorData.const_mem 0,hz⟩
  · obtain ⟨q,C,G,R,hC,ha,he,hl⟩ := hf.sector_leading hz
    exact ⟨G,⟨sector_halfplane_analytic ha,hf.congr he⟩,he⟩

lemma ClockGerm.first_of_lower {X : ℝ → ℝ} (hX : Puiseux (fun t => (X t:ℂ)))
    (hXt : Tendsto X atTop atTop) {f : ℝ → ℂ} (hf : Puiseux f) : ClockGerm (X :: []) f := by
  obtain ⟨I,hI,hIt,hl,hr⟩ := hX.inverse_change hXt
  obtain ⟨F,hF,he⟩ := (hf.comp_unbounded hI hIt).sector_representative
  have hex : SectorExpansion F {0} (fun _ => F) := by
    simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using
      SectorExpansion.single 0 hF.1 (puiseux_lowerSectorData.slow hF)
  apply (firstClock_expansion_iff hX hXt).mpr
  refine ⟨F,⟨{0},fun _ => F,hex,fun _ _ => hF⟩,?_⟩
  filter_upwards [hXt.eventually he,hr] with t ht hr
  simpa only [hr] using ht

lemma ClockGerm.first_deriv {X : ℝ → ℝ} (hX : Puiseux (fun t => (X t:ℂ)))
    (hXt : Tendsto X atTop atTop) {f : ℝ → ℂ} (hf : ClockGerm (X :: []) f) :
    ClockGerm (X :: []) (deriv f) := by
  obtain ⟨F,hF,he⟩ := (firstClock_expansion_iff hX hXt).mp hf
  have hFx : ClockGerm (X :: []) (fun t => deriv F (X t:ℂ)) :=
    (firstClock_expansion_iff hX hXt).mpr ⟨deriv F,hF.puiseux_deriv,EventuallyEq.rfl⟩
  have hX' := ClockGerm.first_of_lower hX hXt hX.real_deriv
  apply (hFx.first_mul hX hXt hX').congr
  have hFa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ F z := by
    obtain ⟨E,b,hF,hb⟩ := hF
    exact hF.eventually_analytic
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  filter_upwards [hX.real_eventually_analytic,
    hXt.eventually (tendsto_real_sectorInfinity.eventually hFa),eventually_gt_atTop T] with t hXa hFa ht
  have hd := hFa.differentiableAt.hasDerivAt.comp_ofReal.scomp t hXa.differentiableAt.hasDerivAt
  have hc : (fun s => F (X s:ℂ)) =ᶠ[𝓝 t] f :=
    (eventually_gt_nhds ht).mono (fun s hs => (hT s hs.le).symm)
  simpa only [Complex.real_smul,mul_comm] using (hd.congr_of_eventuallyEq hc.symm).deriv.symm

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma Puiseux.log_deriv_tendsto {f : ℝ → ℂ} (hf : Puiseux f)
    (hne : ¬ f =ᶠ[atTop] fun _ => 0) :
    Tendsto (fun t => _root_.deriv f t / f t) atTop (𝓝 0) := by
  obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.normalize hne
  let q : ℝ := -(m:ℝ)/(n:ℝ)
  let r : ℝ := -(n:ℝ)⁻¹
  have he' : f =ᶠ[atTop] fun x => ((x^q:ℝ):ℂ)*F (rootCoord n x) := by
    filter_upwards [he,eventually_gt_atTop (0:ℝ)] with x hx hxpos
    simp [hx,rootCoord_zpow hxpos,q,Complex.real_smul]
  have hroot := rootCoord_complex_tendsto_zero hn
  have hlim : Tendsto (fun x : ℝ => (x:ℂ)⁻¹ *
      ((q:ℂ)+(r:ℂ)*(rootCoord n x:ℂ)*_root_.deriv F (rootCoord n x)/F (rootCoord n x)))
      atTop (𝓝 0) := by
    have hbr := (tendsto_const_nhds (x := (q:ℂ))).add
      ((((tendsto_const_nhds (x := (r:ℂ))).mul hroot).mul (hF.deriv.continuousAt.tendsto.comp hroot)).div
        (hF.continuousAt.tendsto.comp hroot) hF0)
    convert! (tendsto_inv_atTop_zero.ofReal.mul hbr) using 1 <;> simp
  apply hlim.congr'
  filter_upwards [eventuallyEq_deriv_atTop he',he',
    hroot.eventually hF.eventually_analyticAt,
    hroot.eventually (hF.continuousAt.eventually_ne hF0),
    eventually_gt_atTop (0:ℝ)] with x hdx hx hFx hFx0 hxpos
  have hdroot : HasDerivAt (rootCoord n) (r*x^(r-1)) x := by
    exact Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')
  have hdF := hFx.differentiableAt.hasDerivAt.comp_ofReal.scomp x hdroot
  have hdp := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hxpos.ne')).ofReal_comp
  have hdprod := hdp.mul hdF
  have hdpeq : _root_.deriv (fun y : ℝ => (y^q:ℝ)*F (rootCoord n y)) x =
      (q*x^(q-1):ℝ)*F (rootCoord n x)+(x^q:ℝ)*(r*x^(r-1):ℝ)*_root_.deriv F (rootCoord n x) := by
    convert! hdprod.deriv using 1; simp only [Function.comp_def,Complex.real_smul]; ring
  rw [hdx,hdpeq,hx]
  have hq : x^(q-1)=x^q/x := by rw [Real.rpow_sub hxpos,Real.rpow_one]
  have hr : x^(r-1)=x^r/x := by rw [Real.rpow_sub hxpos,Real.rpow_one]
  have hx0 : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  have hp0 : ((x^q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hxpos q).ne'
  simp only [Complex.ofReal_mul,hq,hr,
    Complex.ofReal_div]
  change (x:ℂ)⁻¹*((q:ℂ)+(r:ℂ)*(x^r:ℝ)*_root_.deriv F (rootCoord n x)/F (rootCoord n x)) = _
  field_simp [hFx0,hx0,hp0]

lemma PuiseuxSector.tendsto_of_ray {F : ℂ → ℂ} (hF : F∈PuiseuxSector) {c : ℂ}
    (ht : Tendsto (fun t : ℝ => F (t:ℂ)) atTop (𝓝 c)) :
    Tendsto F sectorInfinity (𝓝 c) := by
  have hsub : (fun z => F z-c)∈PuiseuxSector :=
    puiseux_lowerSectorData.add_mem hF (puiseux_lowerSectorData.const_mem (-c))
  have ht0 : Tendsto (fun t : ℝ => F (t:ℂ)-c) atTop (𝓝 0) := by
    simpa using ht.sub (tendsto_const_nhds (x := c))
  suffices hz : Tendsto (fun z => F z-c) sectorInfinity (𝓝 0) by
    convert! hz.add_const c using 1 <;> simp
  by_cases he : (fun t : ℝ => F (t:ℂ)-c) =ᶠ[atTop] fun _ => 0
  · exact tendsto_const_nhds.congr'
      (sector_analytic_eq_of_ray hsub.1 (Eventually.of_forall (fun _ => analyticAt_const)) he).symm
  obtain ⟨G,R,ha,hG,hbound⟩ := hsub.2.sector_modulus_comparable he
  have hFG := sector_analytic_eq_of_ray hsub.1 (sector_halfplane_analytic ha) hG
  apply squeeze_zero_norm' (a := fun z : ℂ => 4*‖F (‖z‖:ℂ)-c‖)
  · filter_upwards [hFG,tendsto_norm_sectorInfinity.eventually (eventually_gt_atTop R)] with z hz hR
    rw [hz]
    exact (hbound z hR).2
  · convert! tendsto_const_nhds.mul (ht0.norm.comp tendsto_norm_sectorInfinity) using 1; simp

lemma PuiseuxSector.log_deriv_tendsto {F : ℂ → ℂ} (hF : F∈PuiseuxSector)
    (hne : ¬ (fun t : ℝ => F (t:ℂ)) =ᶠ[atTop] fun _ => 0) :
    Tendsto (fun z => _root_.deriv F z / F z) sectorInfinity (𝓝 0) := by
  have hq : (fun z => _root_.deriv F z / F z)∈PuiseuxSector := by
    simpa only [div_eq_mul_inv] using puiseux_lowerSectorData.mul_mem
      (PuiseuxSector.deriv_mem hF) (puiseux_lowerSectorData.inv_mem hF)
  apply PuiseuxSector.tendsto_of_ray hq
  apply (hF.2.log_deriv_tendsto hne).congr'
  filter_upwards [tendsto_real_sectorInfinity.eventually hF.1] with t ht
  rw [ht.differentiableAt.hasDerivAt.comp_ofReal.deriv]

end DegeneratingTrees.Clock
end

end OAI
