import Mathlib
import OAI.Probability.SKFluctuations.ScalarZeroPlateau

namespace OAI

/-! Scalar Varying Flattened Continuity. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarFlattenedEnergy_varying_mass_tendsto {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (m : ℕ → ℝ) (hm : ∀ k, 0 < m k) (hm1 : ∀ k, m k ≤ 1)
    {p r : ℕ → ℝ} {q : ℝ} (hp : Tendsto p atTop (𝓝 q)) (hr : Tendsto r atTop (𝓝 q))
    (hpr : ∀ k, p k ≤ r k) :
    Tendsto (fun k => scalarFlattenedEnergy hT α (p k) (r k) (hm k)) atTop
      (𝓝 (scalarPlantedEnergy hT α q)) := by
  have ht : Tendsto (fun k => T*(r k-p k)) atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero] using (hr.sub hp).const_mul T
  have hJ := HeatJet.evolve_varying_mass_terminal_tendsto
    (fun k => (scalarTailJet hT α (r k)).square) (scalarTailJet hT α q).square
    (scalarTailJet_F_tendsto hT α hr) (scalarTailJet_square_tendsto hT α hr) m hm hm1
    (fun k => T*(r k-p k)) (fun k => mul_nonneg hT.le (sub_nonneg.mpr (hpr k))) ht
  let A := rescaledMassProfile α hT
  have hA (s : ℝ) : A.mass s ≤ 1 := (α.property.1 (s/T)).2
  have hd := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun k => ((scalarTailJet hT α (r k)).square.evolve (hm k) (T*(r k-p k))))
    (scalarTailJet hT α q).square hJ.1 hJ.2 (fun _ => A) (fun _ => hA)
    (fun _ => 0) (fun k => Real.toNNReal (T*p k))
  have hl := ((scalarTailJet hT α q).square.nonnegativeProfileTest_window_continuous A hA 0).tendsto
    (0,Real.toNNReal (T*q)) |>.comp
      (tendsto_const_nhds.prodMk_nhds (continuous_real_toNNReal.tendsto (T*q) |>.comp (hp.const_mul T)))
  have hh := (hd.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarFlattenedEnergy,scalarPlantedEnergy,A] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem scalarMinimizer_support_stationarity {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 1)
    (hs : q ∈ (profileStieltjes α).measure.support) :
    scalarPlantedEnergy (zero_lt_one.trans hT) α q=q := by
  let d := min q (1-q)/2
  have hd : 0 < d := by
    dsimp only [d]
    exact div_pos (lt_min hq.1 (sub_pos.mpr hq.2)) (by norm_num)
  have hdq : d ≤ q/2 := by dsimp [d]; linarith [min_le_left q (1-q)]
  have hd1 : d ≤ (1-q)/2 := by dsimp [d]; linarith [min_le_right q (1-q)]
  let δ : ℕ → ℝ := fun k => d/((k:ℝ)+1)
  have hδ (k : ℕ) : 0 < δ k := div_pos hd (by positivity)
  have hδd (k : ℕ) : δ k ≤ d := by
    dsimp only [δ]
    rw [div_le_iff₀ (show (0:ℝ)<(k:ℝ)+1 by positivity)]
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  let p : ℕ → ℝ := fun k => q-δ k
  let r : ℕ → ℝ := fun k => q+δ k
  have hp0 (k : ℕ) : 0 < p k := by dsimp only [p]; linarith [hδd k,hq.1]
  have hpq (k : ℕ) : p k < q := by dsimp only [p]; linarith [hδ k]
  have hqr (k : ℕ) : q < r k := by dsimp only [r]; linarith [hδ k]
  have hr1 (k : ℕ) : r k < 1 := by dsimp only [r]; linarith [hδd k,hq.2]
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul d
    simpa only [δ,mul_one_div,mul_zero] using hh
  have hp : Tendsto p atTop (𝓝 q) := by simpa only [sub_zero] using tendsto_const_nhds.sub hδ0
  have hr : Tendsto r atTop (𝓝 q) := by simpa only [add_zero] using tendsto_const_nhds.add hδ0
  have hm (k : ℕ) : 0 < α.val (p k) :=
    (α.property.1 0).1.trans_lt (scalarMinimizer_strict_origin hT α hα hmin (hp0 k))
  have hn (k : ℕ) : 0 < α.val (r k) :=
    (hm k).trans_le (α.property.2 ((hpq k).trans (hqr k)).le)
  have harea (k) := scalarSupport_local_areas α hs (hpq k) (hqr k)
  have hu (k) := scalarMinimizer_local_upper (zero_lt_one.trans hT) (hp0 k).le
    ((hpq k).trans (hqr k)) (hr1 k).le α hα hmin (hm k) (harea k).1
  have hl (k) := scalarMinimizer_local_lower (zero_lt_one.trans hT) (hp0 k).le
    ((hpq k).trans (hqr k)) (hr1 k).le α hα hmin (hn k) (harea k).2
  have hEu := scalarFlattenedEnergy_varying_mass_tendsto (zero_lt_one.trans hT) α
    (fun k => α.val (p k)) hm (fun k => (α.property.1 (p k)).2) hp hr
    (fun k => ((hpq k).trans (hqr k)).le)
  have hEl := scalarFlattenedEnergy_varying_mass_tendsto (zero_lt_one.trans hT) α
    (fun k => α.val (r k)) hn (fun k => (α.property.1 (r k)).2) hp hr
    (fun k => ((hpq k).trans (hqr k)).le)
  have hdu : Tendsto (fun k => r k+6*T*(r k-p k)) atTop (𝓝 q) := by
    simpa only [sub_self,mul_zero,add_zero] using hr.add ((hr.sub hp).const_mul (6*T))
  have hdl : Tendsto (fun k => p k-6*T*(r k-p k)) atTop (𝓝 q) := by
    simpa only [sub_self,mul_zero,sub_zero] using hp.sub ((hr.sub hp).const_mul (6*T))
  exact le_antisymm (le_of_tendsto_of_tendsto' hEu hdu hu) (le_of_tendsto_of_tendsto' hdl hEl hl)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarMinimizer_plateau_KKT {T p r m : ℝ} (hT : 1 < T)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hsp : p ∈ (profileStieltjes α).measure.support)
    (hsr : r ∈ (profileStieltjes α).measure.support)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    0 < m ∧ m < 1 ∧
    scalarPlantedEnergy (zero_lt_one.trans hT) α p=p ∧
    scalarPlantedEnergy (zero_lt_one.trans hT) α r=r ∧
    (∫ u in p..r, scalarPlantedEnergy (zero_lt_one.trans hT) α u-u)=0 ∧
    (∀ x ∈ Ioo p r, (∫ u in p..x, scalarPlantedEnergy (zero_lt_one.trans hT) α u-u) ≤ 0) ∧
    (∀ x ∈ Ioo p r, 0 ≤ ∫ u in x..r, scalarPlantedEnergy (zero_lt_one.trans hT) α u-u) := by
  have hm : 0 < m := by
    rw [← hf ((p+r)/2) ⟨by linarith,by linarith⟩]
    exact (α.property.1 0).1.trans_lt
      (scalarMinimizer_strict_origin hT α hα hmin (by linarith))
  have hm1 : m < 1 := by
    have he := profileStieltjes_support_strict α hsr
      (show (p+r)/2 < r by linarith) (show r < (r+1)/2 by linarith)
    rw [hf ((p+r)/2) ⟨by linarith,by linarith⟩] at he
    exact he.trans_le (α.property.1 ((r+1)/2)).2
  refine ⟨hm,hm1,scalarMinimizer_support_stationarity hT α hα hmin
    ⟨hp,hpr.trans hr⟩ hsp,scalarMinimizer_support_stationarity hT α hα hmin
    ⟨hp.trans hpr,hr⟩ hsr,?_,?_,?_⟩
  · exact le_antisymm
      (scalarMinimizer_plateau_left_integral_nonpos (zero_lt_one.trans hT) hp hpr hr.le
        α hα hm hm1 hf hsp hmin)
      (scalarMinimizer_plateau_right_integral_nonneg (zero_lt_one.trans hT) hp.le hpr hr
        α hα hm hm1 hf hsr hmin)
  · intro x hx
    exact scalarMinimizer_plateau_left_integral_nonpos (zero_lt_one.trans hT) hp hx.1
      (hx.2.trans hr).le α hα hm hm1 (fun u hu => hf u ⟨hu.1,hu.2.trans hx.2⟩) hsp hmin
  · intro x hx
    exact scalarMinimizer_plateau_right_integral_nonneg (zero_lt_one.trans hT)
      (hp.trans hx.1).le hx.2 hr α hα hm hm1
      (fun u hu => hf u ⟨hx.1.trans hu.1,hu.2⟩) hsr hmin

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem hasDerivWithinAt_endpoints_of_continuous_derivative {f g : ℝ → ℝ} {p r : ℝ}
    (hpr : p < r) (hf : Continuous f) (hg : ContinuousOn g (Icc p r))
    (hd : ∀ u ∈ Ioo p r, HasDerivAt f (g u) u) :
    HasDerivWithinAt f (g p) (Ici p) p ∧ HasDerivWithinAt f (g r) (Iic r) r := by
  have hleft : Ioo p r ∈ 𝓝[>] p :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hpr))
  have hright : Ioo p r ∈ 𝓝[<] r :=
    inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds hpr)) self_mem_nhdsWithin
  have hdiff : DifferentiableOn ℝ f (Ioo p r) :=
    fun u hu => (hd u hu).differentiableAt.differentiableWithinAt
  constructor
  · apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hf.continuousAt.continuousWithinAt hleft
    apply ((hg p ⟨le_rfl,hpr.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset hleft Ioo_subset_Icc_self)).tendsto.congr'
    filter_upwards [hleft] with u hu
    exact (hd u hu).deriv.symm
  · apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hf.continuousAt.continuousWithinAt hright
    apply ((hg r ⟨hpr.le,le_rfl⟩).mono_of_mem_nhdsWithin
      (mem_of_superset hright Ioo_subset_Icc_self)).tendsto.congr'
    filter_upwards [hright] with u hu
    exact (hd u hu).deriv.symm

 theorem scalarPlantedEnergy_plateau_endpoint_derivatives {T p r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpr : p < r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    HasDerivWithinAt (scalarPlantedEnergy hT α)
      (((scalarTailJet hT α r).profileGapEnergyJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) 0).nonnegativeProfileTest
        (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0*T) (Ici p) p ∧
    HasDerivWithinAt (scalarPlantedEnergy hT α)
      (((scalarTailJet hT α r).profileGapEnergyJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(r-p))).nonnegativeProfileTest
        (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0*T) (Iic r) r := by
  have hd : 0 < T*(r-p) := mul_pos hT (sub_pos.mpr hpr)
  have hc := (scalarTailJet hT α r).profileGapEnergy_continuousOn
    (scalarTailJet_G_smooth hT α r) (scalarTailJet_H_smooth hT α r) hm hd
    (rescaledMassProfile α hT) (fun u => (α.property.1 (u/T)).2)
    0 (Real.toNNReal (T*p)) 0
  have hg : ContinuousOn (fun u =>
      ((scalarTailJet hT α r).profileGapEnergyJet (scalarTailJet_G_smooth hT α r)
        hm (T*(r-p)) (T*(u-p))).nonnegativeProfileTest
        (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0*T) (Icc p r) := by
    apply (hc.comp (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn ?_).mul
      continuousOn_const
    intro u hu
    change 0 ≤ T*(u-p) ∧ T*(u-p) ≤ T*(r-p)
    exact ⟨mul_nonneg hT.le (sub_nonneg.mpr hu.1),
      mul_le_mul_of_nonneg_left (by linarith [hu.2]) hT.le⟩
  have hh := hasDerivWithinAt_endpoints_of_continuous_derivative hpr
    (scalarPlantedEnergy_continuous hT α) hg
    (fun u hu => scalarPlantedEnergy_hasDerivAt_plateau hT hp hu hr α hm hm1 hf)
  simpa only [sub_self,mul_zero] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology

 theorem HasDerivWithinAt.nonpos_of_right_integral_nonpos {f : ℝ → ℝ} {p r d : ℝ}
    (hpr : p < r) (hc : Continuous f) (hp : f p=0)
    (hd : HasDerivWithinAt f d (Ici p) p)
    (hi : ∀ x ∈ Ioo p r, (∫ u in p..x, f u) ≤ 0) : d ≤ 0 := by
  by_contra hn
  have hd0 : 0 < d := lt_of_not_ge hn
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (show p ∉ Ioi p by simp)).mp hd.Ioi_of_Ici
  have he : ∀ᶠ x in 𝓝[>] p, 0 < slope f p x := hs.eventually (eventually_gt_nhds hd0)
  obtain ⟨b,hpb,hb⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  change p < b at hpb
  let x := (p+min b r)/2
  have hpx : p < x := by dsimp [x]; have := lt_min hpb hpr; linarith
  have hxb : x < b := by dsimp [x]; have := min_le_left b r; linarith
  have hxr : x < r := by dsimp [x]; have := min_le_right b r; linarith
  have hf (u : ℝ) (hu : u ∈ Ioc p x) : 0 < f u := by
    have hh := hb ⟨hu.1,hu.2.trans hxb.le⟩
    change 0 < slope f p u at hh
    rw [slope_def_field,hp,sub_zero] at hh
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hu.1)).mp hh
  have hh := intervalIntegral.integral_pos hpx hc.continuousOn
    (fun u hu => (hf u hu).le) ⟨x,⟨hpx.le,le_rfl⟩,hf x ⟨hpx,le_rfl⟩⟩
  exact (not_lt_of_ge (hi x ⟨hpx,hxr⟩)) hh

 theorem HasDerivWithinAt.nonpos_of_left_integral_nonneg {f : ℝ → ℝ} {p r d : ℝ}
    (hpr : p < r) (hc : Continuous f) (hr : f r=0)
    (hd : HasDerivWithinAt f d (Iic r) r)
    (hi : ∀ x ∈ Ioo p r, 0 ≤ ∫ u in x..r, f u) : d ≤ 0 := by
  by_contra hn
  have hd0 : 0 < d := lt_of_not_ge hn
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (show r ∉ Iio r by simp)).mp hd.Iio_of_Iic
  have he : ∀ᶠ x in 𝓝[<] r, 0 < slope f r x := hs.eventually (eventually_gt_nhds hd0)
  obtain ⟨b,hbr,hb⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp he
  change b < r at hbr
  let x := (max b p+r)/2
  have hxr : x < r := by dsimp [x]; have := max_lt hbr hpr; linarith
  have hbx : b < x := by dsimp [x]; have := le_max_left b p; linarith
  have hpx : p < x := by dsimp [x]; have := le_max_right b p; linarith
  have hf (u : ℝ) (hu : u ∈ Ico x r) : f u < 0 := by
    have hh := hb ⟨hbx.le.trans hu.1,hu.2⟩
    change 0 < slope f r u at hh
    rw [slope_def_field,hr,sub_zero] at hh
    simpa only [zero_mul] using (lt_div_iff_of_neg (sub_neg.mpr hu.2)).mp hh
  have hh := intervalIntegral.integral_pos hxr hc.neg.continuousOn
    (fun u hu => by
      by_cases hu' : u=r
      · simp [hu',hr]
      · exact neg_nonneg.mpr (hf u ⟨hu.1.le,lt_of_le_of_ne hu.2 hu'⟩).le)
    ⟨x,⟨le_rfl,hxr.le⟩,neg_pos.mpr (hf x ⟨le_rfl,hxr⟩)⟩
  change 0 < ∫ u in x..r, -f u at hh
  rw [intervalIntegral.integral_neg] at hh
  linarith [hi x ⟨hpx,hxr⟩]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarMinimizer_plateau_endpoint_KKT {T p r m : ℝ} (hT : 1 < T)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hsp : p ∈ (profileStieltjes α).measure.support)
    (hsr : r ∈ (profileStieltjes α).measure.support)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    ∃ hm : 0 < m,
    (((scalarTailJet (zero_lt_one.trans hT) α r).profileGapEnergyJet
      (scalarTailJet_G_smooth (zero_lt_one.trans hT) α r) hm (T*(r-p)) 0).nonnegativeProfileTest
      (rescaledMassProfile α (zero_lt_one.trans hT)) 0 (Real.toNNReal (T*p)) 0*T) ≤ 1 ∧
    (((scalarTailJet (zero_lt_one.trans hT) α r).profileGapEnergyJet
      (scalarTailJet_G_smooth (zero_lt_one.trans hT) α r) hm (T*(r-p)) (T*(r-p))).nonnegativeProfileTest
      (rescaledMassProfile α (zero_lt_one.trans hT)) 0 (Real.toNNReal (T*p)) 0*T) ≤ 1 := by
  obtain ⟨hm,hm1,hEp,hEr,_hwhole,hleft,hright⟩ :=
    scalarMinimizer_plateau_KKT hT hp hpr hr α hα hf hsp hsr hmin
  have hd := scalarPlantedEnergy_plateau_endpoint_derivatives (zero_lt_one.trans hT)
    hp.le hpr hr.le α hm hm1.le hf
  have hc : Continuous (fun u => scalarPlantedEnergy (zero_lt_one.trans hT) α u-u) :=
    (scalarPlantedEnergy_continuous (zero_lt_one.trans hT) α).sub continuous_id
  have hp0 : scalarPlantedEnergy (zero_lt_one.trans hT) α p-p=0 := sub_eq_zero.mpr hEp
  have hr0 : scalarPlantedEnergy (zero_lt_one.trans hT) α r-r=0 := sub_eq_zero.mpr hEr
  have hl := HasDerivWithinAt.nonpos_of_right_integral_nonpos hpr hc hp0
    (hd.1.sub (hasDerivAt_id p).hasDerivWithinAt) hleft
  have hr' := HasDerivWithinAt.nonpos_of_left_integral_nonneg hpr hc hr0
    (hd.2.sub (hasDerivAt_id r).hasDerivWithinAt) hright
  exact ⟨hm,by linarith,by linarith⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

theorem scalarMinimizer_no_positive_support_gap {T p r m : ℝ} (hT : 1 < T)
    (hp : 0 < p) (hpr : p < r) (hr : r < 1)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hc : ∀ x ∈ Ico (0:ℝ) r, ContinuousWithinAt α.val (Ici x) x)
    (hf : ∀ u ∈ Ioo p r, α.val u=m)
    (hsp : p ∈ (profileStieltjes α).measure.support)
    (hsr : r ∈ (profileStieltjes α).measure.support)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) : False := by
  let hT0 : 0 < T := zero_lt_one.trans hT
  obtain ⟨hm,hm1,hEp,hEr,_hwhole,_hleft,_hright⟩ :=
    scalarMinimizer_plateau_KKT hT hp hpr hr α hα hf hsp hsr hmin
  obtain ⟨_hm,he0,heD⟩ := scalarMinimizer_plateau_endpoint_KKT hT hp hpr hr α hα hf hsp hsr hmin
  let D := T*(r-p)
  have hD : 0 < D := mul_pos hT0 (sub_pos.mpr hpr)
  let J := scalarTailJet hT0 α r
  let hG := scalarTailJet_G_smooth hT0 α r
  let hH := scalarTailJet_H_smooth hT0 α r
  let β := rescaledMassProfile α hT0
  have hβ : ∀ u, β.mass u ≤ 1 := fun u => (α.property.1 (u/T)).2
  let τ := Real.toNNReal (T*p)
  let E := fun s : ℝ => (J.profileGapEnergyJet hG hm D s).nonnegativeProfileTest β 0 τ 0
  let G := fun s : ℝ => (J.profileGapCurvatureJet hG hm D s).nonnegativeProfileTest β 0 τ 0
  let H := fun s : ℝ => (J.profileGapThirdJet hG hm D s).nonnegativeProfileTest β 0 τ 0
  let Q := fun s : ℝ => scalarPlantedEnergy hT0 α (p+s/T)-(p+s/T)
  have hpos (s : ℝ) (hs : s ∈ Ioo 0 D) : p+s/T ∈ Ioo p r := by
    constructor
    · have hh := div_pos hs.1 hT0; linarith
    · have hh : s/T < r-p := (div_lt_iff₀ hT0).mpr (by
        have hh := hs.2
        dsimp only [D] at hh
        nlinarith)
      linarith
  have hclock (s : ℝ) : T*((p+s/T)-p)=s := by field_simp; ring
  have hQc : Continuous Q :=
    ((scalarPlantedEnergy_continuous hT0 α).comp (continuous_const.add (continuous_id.div_const T))).sub
      (continuous_const.add (continuous_id.div_const T))
  have hEc := J.profileGapEnergy_continuousOn hG hH hm hD β hβ 0 τ 0
  have hGc := J.profileGapCurvature_continuousOn hG hH hm hD β hβ 0 τ 0
  have hEd (s : ℝ) (hs : s ∈ Ioo 0 D) : HasDerivAt E (G s) s :=
    J.profileGapEnergy_hasDerivAt hG hm hH hs β hβ 0 τ 0
  have hGd (s : ℝ) (hs : s ∈ Ioo 0 D) : HasDerivAt G (H s) s :=
    J.profileGapCurvature_hasDerivAt hG hm hH hs β hβ 0 τ 0
  have hroot (s : ℝ) (hs : s ∈ Ioo 0 D) (hz : G s=0) : 0 < H s := by
    have hh := scalarPlateau_root_transversality hT0 hp.le (hpos s hs).1 (hpos s hs).2 hr.le
      α hm hm1.le hf (fun x hx => hc x ⟨hx.1,hx.2.trans (hpos s hs).2⟩)
    have hz' : (((scalarTailJet hT0 α r).profileGapCurvatureJet hG hm
        (T*(r-p)) (T*((p+s/T)-p))).nonnegativeProfileTest β 0 τ 0)=0 := by
      rw [hclock]
      exact hz
    have hh' := hh hz'
    rw [hclock] at hh'
    exact hh'
  have hQd (s : ℝ) (hs : s ∈ Ioo 0 D) : HasDerivAt Q (E s-1/T) s := by
    have hd := scalarPlantedEnergy_hasDerivAt_plateau hT0 hp.le (hpos s hs) hr.le α hm hm1.le hf
    have hl : HasDerivAt (fun u : ℝ => p+u/T) (1/T) s :=
      ((hasDerivAt_id s).div_const T).const_add p
    have hh := (hd.comp s hl).sub hl
    apply hh.congr_deriv
    rw [hclock]
    change (E s*T)*(1/T)-1/T=E s-1/T
    field_simp
  have hQeq : Q 0=Q D := by
    have he : p+D/T=r := by dsimp [D]; field_simp; ring
    dsimp only [Q]
    rw [zero_div,add_zero,hEp,he,hEr]
    ring
  have ha : E 0-1/T ≤ 0 := by
    have hh : E 0*T ≤ 1 := he0
    apply sub_nonpos.mpr
    exact (le_div_iff₀ hT0).mpr hh
  have hb : E D-1/T ≤ 0 := by
    have hh : E D*T ≤ 1 := heD
    apply sub_nonpos.mpr
    exact (le_div_iff₀ hT0).mpr hh
  exact transverse_no_stationary_gap hD (hEc.sub continuousOn_const) hGc
    (fun s hs => (hEd s hs).sub_const (1/T)) hGd hroot hQc.continuousOn hQd hQeq ha hb

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

noncomputable def HeatJet.testProduct (J K : HeatJet 0) : HeatJet 0 :=
  { J with
    A := fun y => J.A y*K.A y
    A₁ := fun i y => J.A₁ i y*K.A y+J.A y*K.A₁ i y
    A₂ := fun i y => J.A₂ i y*K.A y+2*(J.A₁ i y*K.A₁ i y)+J.A y*K.A₂ i y
    smoothA := J.smoothA.mul K.smoothA
    smoothA₁ := fun i => ((J.smoothA₁ i).mul K.smoothA).add (J.smoothA.mul (K.smoothA₁ i))
    smoothA₂ := fun i => (((J.smoothA₂ i).mul K.smoothA).add
      (((J.smoothA₁ i).mul (K.smoothA₁ i)).const_mul 2)).add (J.smoothA.mul (K.smoothA₂ i))
    derivA := by
      intro x v s
      apply ((J.derivA x v s).mul (K.derivA x v s)).congr_deriv
      simp only [Nat.reduceAdd,Fin.sum_univ_one]
      ring
    derivA₁ := by
      intro i x s
      apply (((J.derivA₁ i x s).mul (K.derivA_coord i x s)).add
        ((J.derivA_coord i x s).mul (K.derivA₁ i x s))).congr_deriv
      ring }

noncomputable def HeatJetFamily.testProduct (V W : HeatJetFamily 0) : HeatJetFamily 0 :=
  { V with
    J := fun q => (V.J q).testProduct (W.J q)
    continuousA := V.continuousA.mul W.continuousA
    continuousA₁ := fun i => ((V.continuousA₁ i).mul W.continuousA).add
      (V.continuousA.mul (W.continuousA₁ i))
    continuousA₂ := fun i => (((V.continuousA₂ i).mul W.continuousA).add
      (((V.continuousA₁ i).mul (W.continuousA₁ i)).const_mul 2)).add
        (V.continuousA.mul (W.continuousA₂ i))
    boundedA := V.boundedA.mul W.boundedA
    boundedA₁ := fun i => ((V.boundedA₁ i).mul W.boundedA).add
      (V.boundedA.mul (W.boundedA₁ i))
    boundedA₂ := fun i => (((V.boundedA₂ i).mul W.boundedA).add
      (((V.boundedA₁ i).mul (W.boundedA₁ i)).const_mul 2)).add
        (V.boundedA.mul (W.boundedA₂ i)) }

theorem HeatJet.testAverageRate_zero_scalar (J : HeatJet 0) (m : ℝ) (x : Fin 1 → ℝ) :
    J.testAverageRate m 0 x = J.A₂ 0 x/2+m*J.G 0 x*J.A₁ 0 x := by
  rw [J.testAverageRate_zero]
  simp only [clockTestDerivative,clockTest_zero,testedHeatTrace,potentialHeatTrace,
    Nat.reduceAdd,Fin.sum_univ_one]
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
noncomputable def scalarTailCurvatureRate {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q m t : ℝ) : ℝ :=
  (scalarTailTestJet hT α 1 q).testAverageRate (unitMassClip m) t 0+
    unitMassClip m*(scalarTailJet hT α q).square.testAverageRate (unitMassClip m) t 0-
    unitMassClip m*t*((scalarTailJet hT α q).testAverageRate (unitMassClip m) t 0)^2

theorem scalarTailCurvatureRate_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => scalarTailCurvatureRate hT α p.2.1 p.2.2 p.1) := by
  have hH := (scalarTailTestFamily hT α 1).testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have hA := (scalarTailJetFamily hT α).testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have hA₂ := (scalarTailJetFamily hT α).square.testAverageRate_continuous_mass (0:Fin 1 → ℝ)
  have hm := unitMassClip_continuous.comp (continuous_snd.snd : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2))
  exact (hH.add (hm.mul hA₂)).sub ((hm.mul continuous_fst).mul (hA.pow 2))

theorem scalarTailCurvatureRate_zero {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (q m : ℝ) :
    scalarTailCurvatureRate hT α q m 0 = scalarTailSpatialJet hT α 4 q 0/2+
      unitMassClip m*((scalarTailJet hT α q).H 0 0)^2 := by
  have hz := scalarTailJet_A_zero hT α q
  unfold scalarTailCurvatureRate
  rw [HeatJet.testAverageRate_zero_scalar,HeatJet.testAverageRate_zero_scalar]
  change scalarTailSpatialJet hT α 4 q 0/2+
    unitMassClip m*(scalarTailJet hT α q).A 0*scalarTailSpatialJet hT α 3 q 0+
    unitMassClip m*((2*(((scalarTailJet hT α q).H 0 0)^2+
      (scalarTailJet hT α q).A 0*(scalarTailJet hT α q).A₂ 0 0))/2+
      unitMassClip m*(scalarTailJet hT α q).A 0*(2*((scalarTailJet hT α q).A 0*(scalarTailJet hT α q).H 0 0)))-
    unitMassClip m*0*_ = _
  rw [hz]
  ring

theorem scalarTailCurvatureRate_eq {T q m t : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (ht : 0 ≤ t) :
    ((scalarTailJet hT α q).evolve hm t).H 0 0 = (scalarTailJet hT α q).H 0 0+
      t*scalarTailCurvatureRate hT α q m t := by
  let J := scalarTailJet hT α q
  have h0 : J.A 0 = 0 := scalarTailJet_A_zero hT α q
  have hh := (scalarTailTestJet hT α 1 q).testAverageRate_eq m ht (0:Fin 1 → ℝ)
  have ha := J.testAverageRate_eq m ht (0:Fin 1 → ℝ)
  have hs := J.square.testAverageRate_eq m ht (0:Fin 1 → ℝ)
  change clockTest m J.F (J.H 0) t 0 = J.H 0 0+t*_ at hh
  change clockTest m J.F (fun y => (J.A y)^2) t 0 = (J.A 0)^2+t*_ at hs
  rw [h0] at ha hs
  change clockGradient m J.F (J.A) (J.A) (J.H 0) t 0 = _
  unfold clockGradient
  have hf : (fun y => J.A y*J.A y) = fun y => (J.A y)^2 := by funext y; ring
  rw [hf,hh,ha,hs]
  unfold scalarTailCurvatureRate
  rw [unitMassClip_eq ⟨hm.le,hm1⟩]
  change _ = J.H 0 0+t*((scalarTailTestJet hT α 1 q).testAverageRate m t 0+
    m*J.square.testAverageRate m t 0-m*t*(J.testAverageRate m t 0)^2)
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTailJet_flatten_signed_error_source {T q r m : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hm1 : m ≤ 1) (x : Fin 1 → ℝ) :
    |clockContinuation m (scalarTailJet hT α q).F (T*q) x-
      clockContinuation m (scalarTailJet hT α r).F (T*r) x-
      (T/2*(∫ s in q..r, α.val s-m))*(scalarTailJet hT α r).observedSquare m (T*r) x| ≤
      2*T^2*(r-q)^2 := by
  have hs : 0 ≤ T*(r-q) := mul_nonneg hT.le (sub_nonneg.mpr hqr)
  have he : T*q+T*(r-q)=T*r := by ring
  have hi : (∫ s in T*q..T*r, (rescaledMassProfile α hT).mass s-m) =
      T*(∫ s in q..r, α.val s-m) := by
    change (∫ s in T*q..T*r, (fun z => α.val z-m) (s/T)) = _
    rw [intervalIntegral.integral_comp_div (fun z => α.val z-m) hT.ne']
    simp only [mul_div_cancel_left₀ _ hT.ne',smul_eq_mul]
  have hh := HeatJet.flatten_profile_signed_error (scalarTailJet_admissible hT α r)
    (scalarTailJet_gradientTest hT α r) (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) (A:=T*q) (l:=T*q)
    (Real.toNNReal (T*(r-q))) hm hm1
    (mul_nonneg hT.le hq) (scalarTailJet_restart hT hqr hr α) x
  simp only [Real.coe_toNNReal _ hs,he,hi] at hh
  rw [show T*(∫ s in q..r, α.val s-m)/2 = T/2*(∫ s in q..r, α.val s-m) by ring] at hh
  exact hh.trans_eq (by ring)

theorem scalarTailJet_observedSquare_continuous_source {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (m : ℝ) (x : Fin 1 → ℝ) :
    Continuous (fun q => (scalarTailJet hT α q).observedSquare m (T*q) x) :=
  HeatJet.observedSquare_continuous (J:=scalarTailJet hT α)
    (scalarTailJet_lipschitz hT α) (scalarTailJet_F_continuous hT α)
    (scalarTailJet_square_continuous hT α) (scalarTailJet_square_bound hT α) m T x

theorem scalarTailJet_flatten_hasDerivWithinAt_source {T q m : ℝ} (hT : 0 < T)
    (hq : 0 ≤ q) (hq1 : q < 1) (α : boundedMassProfiles)
    (hm : 0 < m) (hm1 : m ≤ 1) (hc : ContinuousWithinAt α.val (Ici q) q) (x : Fin 1 → ℝ) :
    HasDerivWithinAt
      (fun r => clockContinuation m (scalarTailJet hT α r).F (T*r) x)
      (T/2*(m-α.val q)*(scalarTailJet hT α q).observedSquare m (T*q) x)
      (Ioi q) q := by
  have hi : HasDerivWithinAt (fun r => ∫ s in q..r, α.val s-m)
      (α.val q-m) (Ici q) q :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (α.property.2.intervalIntegrable.sub intervalIntegrable_const)
      (α.property.2.measurable.sub measurable_const).stronglyMeasurable.stronglyMeasurableAtFilter
      ((hc.mono Ioi_subset_Ici_self).sub continuousWithinAt_const)
  have hd := right_derivative_of_quadratic_remainder
    ((hi.mono Ioi_subset_Ici_self).const_mul (T/2))
    ((scalarTailJet_observedSquare_continuous_source hT α m x).continuousWithinAt (s:=Ioi q) (x:=q))
    (C:=2*T^2) (F:=fun r => clockContinuation m (scalarTailJet hT α r).F (T*r) x)
    (by
      filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ r : ℝ in 𝓝[>] q, r < 1 from
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hq1))] with r hr hr1
      simpa only [intervalIntegral.integral_same,mul_zero,sub_zero] using
        scalarTailJet_flatten_signed_error_source hT hq hr.le hr1.le α hm hm1 x)
  convert hd using 1; ring

theorem scalarTailJet_flatten_continuous_source {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (m : ℝ) (x : Fin 1 → ℝ) :
    Continuous (fun q => clockContinuation m (scalarTailJet hT α q).F (T*q) x) :=
  (dynamic_clockContinuation_continuous (scalarTailJet_lipschitz hT α)
    (scalarTailJet_F_continuous hT α) m x).comp
    ((continuous_const.mul continuous_id).prodMk continuous_id)

 

theorem scalarTailJet_flatten_difference_source {T q r m : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) (x : Fin 1 → ℝ) :
    clockContinuation m (scalarTailJet hT α r).F (T*r) x-
      clockContinuation m (scalarTailJet hT α q).F (T*q) x =
      T/2*(∫ s in q..r, (m-α.val s)*(scalarTailJet hT α s).observedSquare m (T*s) x) := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hqr
    (scalarTailJet_flatten_continuous_source hT α m x).continuousOn
    (f':=fun s => T/2*(m-α.val s)*(scalarTailJet hT α s).observedSquare m (T*s) x)
    (fun s hs => scalarTailJet_flatten_hasDerivWithinAt_source hT (hq.trans hs.1.le)
      (hs.2.trans_le hr) α hm hm1 (hc s) x)
    (((intervalIntegrable_const.sub α.property.2.intervalIntegrable).const_mul (T/2)).mul_continuousOn
      (scalarTailJet_observedSquare_continuous_source hT α m x).continuousOn)
  rw [← hh,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem weighted_profile_integral_hasDerivAt {f g : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ s x, HasDerivAt (fun y => f (s,y)) (g (s,x)) x)
    (α : boundedMassProfiles) (m a b x : ℝ) :
    HasDerivAt (fun y => ∫ s in a..b, (m-α.val s)*f (s,y))
      (∫ s in a..b, (m-α.val s)*g (s,x)) x := by
  have hS : IsCompact (Icc (min a b) (max a b) ×ˢ Icc (x-1) (x+1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨K,hK⟩ := hS.bddAbove_image hg.norm.continuousOn
  have hK' (s y : ℝ) (hs : s ∈ Icc (min a b) (max a b)) (hy : y ∈ Icc (x-1) (x+1)) :
      |g (s,y)| ≤ max K 0 :=
    (hK ⟨(s,y),⟨hs,hy⟩,rfl⟩).trans (le_max_left _ _)
  have hweight (s : ℝ) : |m-α.val s| ≤ |m|+1 := by
    have hh := abs_sub m (α.val s)
    rw [abs_of_nonneg (α.property.1 s).1] at hh
    linarith [(α.property.1 s).2]
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun y s => (m-α.val s)*f (s,y))
    (F':=fun y s => (m-α.val s)*g (s,y))
    (bound:=fun _ => (|m|+1)*max K 0)
    (s:=Ioo (x-1) (x+1)) (Ioo_mem_nhds (by linarith) (by linarith)) _ _ _ _
    intervalIntegrable_const _).2
  · exact Eventually.of_forall fun y =>
      ((measurable_const.sub α.property.2.measurable).mul
        (hf.comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable
  · exact (intervalIntegrable_const.sub α.property.2.intervalIntegrable).mul_continuousOn
      (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
  · exact ((measurable_const.sub α.property.2.measurable).mul
      (hg.comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable
  · exact ae_of_all volume fun s hs y hy => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hweight s) (hK' s y (uIoc_subset_uIcc hs) ⟨hy.1.le,hy.2.le⟩)
        (abs_nonneg _) (by positivity)
  · exact ae_of_all volume fun s _ y _ => (hd s y).const_mul (m-α.val s)

end SKFluctuations.Hierarchy

end

end OAI
