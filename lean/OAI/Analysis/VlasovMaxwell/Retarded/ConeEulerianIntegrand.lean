import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.BinHits

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma physicalBin_integral_eq_triangle {V : ℝ → Vec} (hV : Measurable V)
    (C : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) {T : ℝ} (hJT : J⊆Icc 0 T)
    {g : ConeCoordinate → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z,g z ∂physicalBinMeasure V C J) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) t, ∫⁻ n : Sphere,
        (physicalBinBase V C J).indicator g (t,r,n) ∂sphereMeasure := by
  have hbase := measurableSet_physicalBinBase hV C hJ
  unfold physicalBinMeasure
  rw [← lintegral_indicator hbase,lintegral_prod _ (hg.indicator hbase).aemeasurable]
  simp_rw [restrict_Ioo_eq_restrict_Icc]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  have hm : Measurable (fun p : ℝ × Sphere => (physicalBinBase V C J).indicator g (t,p)) :=
    (hg.indicator hbase).comp (measurable_const.prodMk measurable_id)
  by_cases ht : t∈Icc 0 T
  · rw [indicator_of_mem ht,lintegral_prod _ hm.aemeasurable,← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro r
    by_cases hr : r∈Icc 0 t
    · rw [indicator_of_mem hr]
    · rw [indicator_of_notMem hr]
      apply lintegral_eq_zero_of_ae_eq_zero
      apply ae_of_all
      intro n
      exact indicator_of_notMem (fun hz => hr hz.2.1) _
  · rw [indicator_of_notMem ht]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro p
    exact indicator_of_notMem (fun hz => ht (hJT hz.1)) _

def coneEulerianIntegrand (s : Solution) (T : ℝ) (X V : ℝ → Vec)
    (H : Set (ℝ × Phase)) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1)))) *
    ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (prefixParticle s T p))
      (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))

lemma measurable_coneEulerianIntegrand {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    (hT : 0≤T) {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    Measurable (coneEulerianIntegrand s T X V H) := by
  have hn : Measurable (fun z : ConeCoordinate => z.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hW : Measurable (fun z : ConeCoordinate =>
      ENNReal.ofReal ((z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1))))) :=
    (((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).mul
      (measurable_const.sub (continuous_dot.measurable.comp
        (hn.prodMk ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))).ennreal_ofReal
  have hk : Measurable (fun p : ConeCoordinate × Vec =>
      H.indicator (fun p => ENNReal.ofReal (prefixParticle s T p))
        (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2))) := by
    apply ((hs.continuous_prefixParticle hT).measurable.ennreal_ofReal.indicator hH).comp
    exact (measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub
          (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul (hn.comp measurable_fst))).prodMk measurable_snd)
  exact hW.mul hk.lintegral_prod_right'

lemma PhaseFlowOn.cone_occupation_eq_receiver_coordinates {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    coneOccupation F.flow zX T s.f H =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) t, ∫⁻ n : Sphere,
        coneEulerianIntegrand s T (fun t => (prefixFlow F.flow T zX t).1)
          (fun t => (prefixFlow F.flow T zX t).2) H (t,r,n) ∂sphereMeasure := by
  have hα : Continuous (fun t => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hg := measurable_coneEulerianIntegrand hs hT hα.fst.measurable hα.snd.measurable hH
  rw [← lintegral_retarded_triangle_parameter sphereMeasure T hg]
  unfold coneOccupation
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  apply lintegral_congr
  intro n
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro R hR
  have ht : r+R∈Icc 0 T := ⟨by linarith [hr.1,hR.1],by linarith [hR.2]⟩
  simp only [coneEulerianIntegrand,prefixFlow,prefixClamp_eq ht,add_sub_cancel_left]
  congr 1
  apply lintegral_congr
  intro v
  by_cases hp : (r,((F.flow zX (r+R)).1-R • n.1,v))∈H
  · rw [indicator_of_mem hp,indicator_of_mem hp,prefixParticle,prefixClamp_eq (Ioo_subset_Icc_self hr)]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp]

lemma PhaseFlowOn.physical_bin_point_mem {E B : Field} {T a b c d t r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
    (n : Sphere) (v : Vec) (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T)
    (hr : r∈Ioo 0 T) (hrC : r∈Icc c d) (hrt : r<t) (htT : t<T)
    (hb : (t,r,n)∈physicalBinBase (fun t => (F.flow zX t).2) C (Icc a b))
    (hv : v∈coneBinMomentumSet C n.1 (velocity (F.flow zX t).2))
    (hz : inversePhase F.flow (r,((F.flow zX t).1-(t-r) • n.1,v))∈S) :
    (r,((F.flow zX t).1-(t-r) • n.1,v))∈closedBinEulerian F.flow zX T C S a b c d := by
  let z := inversePhase F.flow (r,((F.flow zX t).1-(t-r) • n.1,v))
  have hflow : F.flow z r=((F.flow zX t).1-(t-r) • n.1,v) :=
    F.flow_inversePhase (Ioo_subset_Icc_self hr) _
  have hR : 0<t-r := sub_pos.mpr hrt
  have hΔ : (F.flow zX t).1-(F.flow z r).1=(t-r) • n.1 := by
    rw [hflow]
    dsimp only
    abel
  have hnorm : t-r=‖(F.flow zX t).1-(F.flow z r).1‖ := by
    rw [hΔ,norm_smul,Real.norm_eq_abs,abs_of_pos hR,sphere_norm,mul_one]
  have hn : (t-r)⁻¹ • ((F.flow zX t).1-(F.flow z r).1)=n.1 := by
    rw [hΔ,smul_smul,inv_mul_cancel₀ hR.ne',one_smul]
  have hbin : InClosedConeBin F.flow zX C t r z := by
    apply (inClosedConeBin_iff hR).mpr
    rw [hn,hflow]
    refine ⟨?_,hb.2.2.1,hv.1,hb.2.2.2.1,hv.2.1,hb.2.2.2.2,hv.2.2⟩
    simpa only [hflow] using hnorm
  have hh : r∈closedBinHits F.flow zX C S a b c d z := ⟨hz,hrC,t,hb.1,hbin⟩
  have ha := F.physical_hit_arrival zX ((F.flow z r).1) hr (hJ hb.1) hrt hnorm htT
  have hd : (r,F.flow z r)∈spaceConeDomain F.flow zX T := by
    refine ⟨hr,?_⟩
    rw [mem_ball,dist_eq_norm']
    linarith [ha.1.2.1]
  have he := (F.mem_closedBinEulerian_iff zX z C S hC).mpr ⟨hh,hd⟩
  simpa only [hflow] using he

lemma PhaseFlowOn.physicalBinDensity_le_Eulerian {s : Solution} {T a b c d t r : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX : Phase) (C : ClosedConeBin) {S : Set Phase}
    (hS : tsupport (fun z => s.f (0,z))⊆S) (n : Sphere)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T)
    (hr : r∈Ioo 0 T) (hrC : r∈Icc c d) (hrt : r<t) (htT : t<T)
    (hb : (t,r,n)∈physicalBinBase (fun t => (F.flow zX t).2) C (Icc a b)) :
    physicalBinDensity s (fun t => (F.flow zX t).1) (fun t => (F.flow zX t).2) C t r n ≤
      ∫⁻ v : Vec, (closedBinEulerian F.flow zX T C S a b c d).indicator
        (fun p => ENNReal.ofReal (s.f p)) (r,((F.flow zX t).1-(t-r) • n.1,v)) := by
  unfold physicalBinDensity
  rw [← lintegral_indicator (measurableSet_coneBinMomentumSet C _ _)]
  apply lintegral_mono
  intro v
  dsimp only
  by_cases hv : v∈coneBinMomentumSet C n.1 (velocity (F.flow zX t).2)
  · rw [indicator_of_mem hv]
    by_cases hf : s.f (r,((F.flow zX t).1-(t-r) • n.1,v))=0
    · rw [hf,ENNReal.ofReal_zero]
      exact bot_le
    · have hf0 : s.f (0,inversePhase F.flow (r,((F.flow zX t).1-(t-r) • n.1,v)))≠0 := by
        rwa [← F.transport_inverse hs.f_smooth hs.vlasov (Ioo_subset_Icc_self hr)]
      have hz := hS (subset_tsupport _ hf0)
      rw [indicator_of_mem (F.physical_bin_point_mem zX C S n v hJ hC hr hrC hrt htT hb hv hz)]
  · rw [indicator_of_notMem hv]
    exact bot_le

end RVM

end

end OAI
