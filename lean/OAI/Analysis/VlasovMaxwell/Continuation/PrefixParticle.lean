import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.RetardedSameTimeSeparation
import OAI.Analysis.VlasovMaxwell.Retarded.SourceCellLast

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma PhaseFlowOn.physical_hit_arrival {E B : Field} {T r t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (y : Vec)
    (hr : r∈Ioo 0 T) (ht : t∈Icc 0 T) (hrt : r<t)
    (he : t-r=‖(F.flow zX t).1-y‖) (htT : t<T) :
    (r,y)∈arrivalDomain F.flow zX T ∧ arrivalTime F.flow zX T (r,y)=t := by
  have hT : 0≤T := hr.1.le.trans hr.2.le
  have hmono := F.arrival_strictMono hT zX y
  have htip : (F.flow zX r).1≠y := by
    intro h
    have hm := hmono (Ioo_subset_Icc_self hr) ht hrt
    dsimp only at hm
    rw [h,sub_self,norm_zero] at hm
    linarith
  have hlast : r+‖(F.flow zX T).1-y‖<T := by
    have hm := hmono ht ⟨hT,le_rfl⟩ htT
    dsimp only at hm
    linarith
  have hp : (r,y)∈arrivalDomain F.flow zX T := ⟨hr,hlast,htip⟩
  refine ⟨hp,?_⟩
  obtain ⟨hτ,hτe⟩ := F.arrival_time_spec zX hp
  apply hmono.injOn ⟨hr.1.le.trans hτ.1.le,hτ.2.le⟩ ht
  dsimp only
  linarith

lemma dyadicWindow_one_inv {x : ℝ} (n : ℕ)
    (hlo : (2:ℝ)^n/2≤x) (hhi : x≤2*(2:ℝ)^n) :
    DyadicWindow 1 n x⁻¹ := by
  have hpow : 0<(2:ℝ)^n := by positivity
  have hx : 0<x := lt_of_lt_of_le (by positivity) hlo
  change 1/(2:ℝ)^1≤(2:ℝ)^n*x⁻¹ ∧ (2:ℝ)^n*x⁻¹≤(2:ℝ)^1
  rw [pow_one,← div_eq_mul_inv]
  constructor
  · apply (le_div_iff₀ hx).mpr
    linarith
  · apply (div_le_iff₀ hx).mpr
    linarith

lemma dyadicWindow_one_sqrt {D : ℝ} (j : ℕ)
    (hlo : ((2:ℝ)^j)⁻¹^2/2≤D) (hhi : D≤8*((2:ℝ)^j)⁻¹^2) :
    DyadicWindow 1 j (Real.sqrt (D/2)) := by
  have hp : 0<(2:ℝ)^j := by positivity
  have hi : 0<((2:ℝ)^j)⁻¹ := inv_pos.mpr hp
  have hD0 : 0≤D := (by positivity : 0≤((2:ℝ)^j)⁻¹^2/2).trans hlo
  have hD : 0≤D/2 := by positivity
  have hsq := Real.sq_sqrt hD
  have hlo' : ((2:ℝ)^j)⁻¹/2≤Real.sqrt (D/2) := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  have hhi' : Real.sqrt (D/2)≤2*((2:ℝ)^j)⁻¹ := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo' hp.le
    simpa only [pow_one,← mul_div_assoc,mul_inv_cancel₀ hp.ne'] using hh
  · have hh := mul_le_mul_of_nonneg_left hhi' hp.le
    simpa only [pow_one,mul_left_comm,mul_inv_cancel₀ hp.ne',mul_one] using hh

lemma PhaseFlowOn.closedBinHit_in_arrivalBudget {E B : Field} {T r t : ℝ}
    (F : PhaseFlowOn E B T) (zX z : Phase) (C : ClosedConeBin) (i j : ℕ)
    (hr : r∈Ioo 0 T) (ht : t∈Icc 0 T) (hR : 0<C.rmin)
    (hiq : (2:ℝ)^i/2≤C.qmin) (hiQ : C.qmax≤2*(2:ℝ)^i)
    (hjD : ((2:ℝ)^j)⁻¹^2/2≤C.Dmin) (hjU : C.Dmax≤8*((2:ℝ)^j)⁻¹^2)
    (hbin : InClosedConeBin F.flow zX C t r z) :
    (r,F.flow z r)∈arrivalBudgetSet F.flow zX T 1 (i,j) := by
  have hrt : 0<t-r := hR.trans_le hbin.2.1.1
  have hh := (inClosedConeBin_iff hrt).mp hbin
  refine ⟨dyadicWindow_one_inv i (hiq.trans hh.2.2.1.1) (hh.2.2.1.2.trans hiQ),?_⟩
  have hangle := dyadicWindow_one_sqrt j
    (hjD.trans hh.2.2.2.2.2.1.1) (hh.2.2.2.2.2.1.2.trans hjU)
  rcases lt_or_eq_of_le ht.2 with htT|rfl
  · left
    have ha := F.physical_hit_arrival zX (F.flow z r).1 hr ht (by linarith) hh.1 htT
    refine ⟨ha.1,?_⟩
    simpa only [arrivalDirection,arrivalRadius,arrivalVelocity,ha.2] using hangle
  · right
    exact ⟨⟨hr,by linarith [hh.1]⟩,hangle⟩

def prefixParticle (s : Solution) (T : ℝ) (p : ℝ × Phase) : ℝ :=
  s.f (prefixClamp T p.1,p.2)

def prefixField (E : Field) (T : ℝ) (p : ℝ × Vec) : Vec :=
  E (prefixClamp T p.1,p.2)

lemma EnergyPrefix.continuous_prefixParticle {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) : Continuous (prefixParticle s T) :=
  hs.f_smooth.continuousOn.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

lemma continuous_prefixField {E : Field} {T : ℝ}
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec))) (hT : 0 ≤ T) :
    Continuous (prefixField E T) :=
  hE.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

lemma measurable_coneBinDensity {g : Particle} (hg : Measurable g)
    {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin) :
    Measurable (fun z : ConeCoordinate => ∫⁻ v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal (g (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))) := by
  let H : Set (ConeCoordinate × Vec) :=
    {p | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}
  have hn : Measurable (fun p : ConeCoordinate × Vec => p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate × Vec => velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate × Vec => velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp (measurable_fst.comp measurable_fst))
  have hH : MeasurableSet H := by
    exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
      ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
        (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))
  have hf : Measurable (fun p : ConeCoordinate × Vec =>
      ENNReal.ofReal (g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) := by
    exact (hg.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul hn)).prodMk
        measurable_snd))).ennreal_ofReal
  have hm : Measurable (fun z : ConeCoordinate =>
      ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (g (p.1.2.1,
        (X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) (z,v)) :=
    (hf.indicator hH).lintegral_prod_right'
  convert hm using 1
  ext z
  rw [← lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
  apply lintegral_congr
  intro v
  rfl

lemma physicalBinDensity_aemeasurable {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    (hT : 0 ≤ T) {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (fun z : ConeCoordinate => physicalBinDensity s X V B z.1 z.2.1 z.2.2)
      (physicalBinMeasure V B J) := by
  have hm := (measurable_coneBinDensity (hs.continuous_prefixParticle hT).measurable hX hV B).aemeasurable
    (μ := physicalBinMeasure V B J)
  apply hm.congr
  apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B hJ)
  intro z hz
  unfold physicalBinDensity
  apply lintegral_congr
  intro v
  rw [prefixParticle,prefixClamp_eq (show z.2.1∈Icc 0 T from ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩)]

lemma physicalBin_integral_le_budget {V : ℝ → Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (k j : ℕ)
    (hangle : ∀ D∈Icc B.Dmin B.Dmax, DyadicWindow k j (Real.sqrt (D/2)))
    {g : ConeCoordinate → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g z ∂physicalBinMeasure V B J) ≤
      ∫⁻ t in J, ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
        (receiverAngularSet (fun t => velocity (V t)) k j t).indicator
          (fun n => g (t,r,n)) n ∂sphereMeasure := by
  have hbase := measurableSet_physicalBinBase hV B hJ
  unfold physicalBinMeasure
  rw [← lintegral_indicator hbase,lintegral_prod _ (hg.indicator hbase).aemeasurable]
  rw [← lintegral_indicator hJ]
  apply lintegral_mono
  intro t
  by_cases ht : t∈J
  · rw [indicator_of_mem ht]
    have hm : Measurable (fun p : ℝ × Sphere => (physicalBinBase V B J).indicator g (t,p)) :=
      (hg.indicator hbase).comp (measurable_const.prodMk measurable_id)
    dsimp only
    rw [lintegral_prod _ hm.aemeasurable,← lintegral_indicator measurableSet_Icc]
    apply lintegral_mono
    intro r
    by_cases hr : r∈Icc 0 t
    · rw [indicator_of_mem hr]
      apply lintegral_mono
      intro n
      dsimp only
      by_cases hz : (t,r,n)∈physicalBinBase V B J
      · rw [indicator_of_mem hz,indicator_of_mem (show n∈receiverAngularSet
          (fun t => velocity (V t)) k j t from hangle _ hz.2.2.2.2)]
      · rw [indicator_of_notMem hz]
        exact bot_le
    · rw [indicator_of_notMem hr]
      apply le_of_eq
      apply lintegral_eq_zero_of_ae_eq_zero
      apply ae_of_all
      intro n
      exact indicator_of_notMem (fun hz => hr hz.2.1) _
  · rw [indicator_of_notMem ht]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro p
    exact indicator_of_notMem (fun hz => ht hz.1) _

def prefixConeGood (s : Solution) (T : ℝ) (X : ℝ → Vec) (z : ConeCoordinate) : ℝ :=
  goodField (prefixField s.E T (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
    (prefixField s.B T (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1

lemma EnergyPrefix.measurable_prefixConeGood {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) {X : ℝ → Vec} (hX : Measurable X) :
    Measurable (prefixConeGood s T X) := by
  have hn : Measurable (fun z : ConeCoordinate => z.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hy : Measurable (fun z : ConeCoordinate =>
      (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) :=
    (measurable_fst.comp measurable_snd).prodMk
      ((hX.comp measurable_fst).sub ((measurable_fst.sub (measurable_fst.comp measurable_snd)).smul hn))
  have hE := (continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy
  have hB := (continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy
  exact (hE.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hn.prodMk hB))).norm.add
    (continuous_dot.measurable.comp (hn.prodMk hB)).abs

lemma EnergyPrefix.physicalBin_goodField {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) {X V : ℝ → Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin) (k j : ℕ)
    (hJ : Icc lo hi⊆Icc 0 T) (hI : 0<I)
    (hangle : ∀ D∈Icc B.Dmin B.Dmax, DyadicWindow k j (Real.sqrt (D/2))) :
    (∫⁻ z : ConeCoordinate, ENNReal.ofReal ((z.1-z.2.1)^2 * prefixConeGood s T X z^2)
      ∂physicalBinMeasure V B (Icc lo hi)) ≤
      ENNReal.ofReal I * goodFieldBudget s X (fun t => velocity (V t)) k lo hi I j := by
  have hg : Measurable (fun z : ConeCoordinate =>
      ENNReal.ofReal ((z.1-z.2.1)^2 * prefixConeGood s T X z^2)) :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2 |>.mul
      ((hs.measurable_prefixConeGood hT hX).pow_const 2)).ennreal_ofReal
  have hbound := physicalBin_integral_le_budget hV B (J:=Icc lo hi) measurableSet_Icc k j hangle hg
  have heq : (∫⁻ t in Icc lo hi, ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
      (receiverAngularSet (fun t => velocity (V t)) k j t).indicator
        (fun n => ENNReal.ofReal ((t-r)^2 * prefixConeGood s T X (t,r,n)^2)) n ∂sphereMeasure) =
      ∫⁻ t in Icc lo hi, goodFieldBinConeMass s X (fun t => velocity (V t)) k j t := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    apply setLIntegral_congr_fun measurableSet_Icc
    intro r hr
    apply lintegral_congr
    intro n
    have hrT : r∈Icc 0 T := ⟨hr.1,hr.2.trans (hJ ht).2⟩
    simp only [prefixConeGood,prefixField,prefixClamp_eq hrT]
  rw [heq] at hbound
  unfold goodFieldBudget
  rw [← mul_assoc,ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top,one_mul]
  exact hbound

end RVM

end

end OAI
