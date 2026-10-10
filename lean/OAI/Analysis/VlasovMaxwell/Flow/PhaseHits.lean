import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.RetardedPhaseDomain
import OAI.Analysis.VlasovMaxwell.Population.LabelOccupation

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma lintegral_radial_measure {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2) * f r := by
  have hpow : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1^2)) :=
    (measurable_subtype_coe.pow_const 2).ennreal_ofReal
  calc
    _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1^2) * f r.1 ∂volume.comap Subtype.val :=
      lintegral_withDensity_eq_lintegral_mul _ hpow (hf.comp measurable_subtype_coe)
    _ = _ := lintegral_subtype_comap (μ := volume) measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r^2) * f r)

lemma lintegral_polar {f : Vec → ENNReal} (hf : Measurable f) :
    (∫⁻ y : Vec, f y) = ∫⁻ n : Sphere, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r^2) * f (r • n.1) ∂volume ∂sphereMeasure := by
  calc
    _ = ∫⁻ z : ({0}ᶜ : Set Vec), f z.1 ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl f,restrict_compl_singleton]
    _ = ∫⁻ p : Sphere × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
      simpa only [Homeomorph.symm_apply_apply,homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin,Nat.reduceSub] using h
    _ = ∫⁻ n : Sphere, ∫⁻ r : Ioi (0 : ℝ), f (r.1 • n.1) ∂Measure.volumeIoiPow 2
        ∂sphereMeasure := by
      apply lintegral_prod
      exact (hf.comp ((measurable_subtype_coe.comp measurable_snd).smul
        (measurable_subtype_coe.comp measurable_fst))).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro n
      exact lintegral_radial_measure (hf.comp (measurable_id.smul_const _))

lemma PhaseFlowOn.receiver_lintegral {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) (g : Vec → ENNReal) :
    ∫⁻ y in ball (F.flow z T).1 (T-s), g y =
      ∫⁻ w in receiverRadialDomain s T,
        ENNReal.ofReal (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) *
          g (receiverRadial F.flow z s w) := by
  have hd : ∀ w ∈ receiverRadialDomain s T,
      HasFDerivWithinAt (receiverRadial F.flow z s)
        (fderiv ℝ (receiverRadial F.flow z s) w) (receiverRadialDomain s T) w := by
    intro w hw
    exact (F.receiver_differential hs.1 z hw).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  calc
    _ = ∫⁻ y in receiverRadial F.flow z s '' receiverRadialDomain s T, g y := by
      apply setLIntegral_congr
      rw [F.receiver_image hs z]
      exact (sdiff_null_ae_eq_self (measure_singleton (F.flow z s).1)).symm
    _ = ∫⁻ w in receiverRadialDomain s T,
        ENNReal.ofReal |(fderiv ℝ (receiverRadial F.flow z s) w).det| *
          g (receiverRadial F.flow z s w) :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (isOpen_receiverRadialDomain s T).measurableSet
        hd (F.receiver_injective hs z) g
    _ = _ := by
      apply setLIntegral_congr_fun (isOpen_receiverRadialDomain s T).measurableSet
      intro w hw
      dsimp only
      rw [F.receiver_jacobian hs.1 z hw]

lemma PhaseFlowOn.lintegral_comp {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (g : Phase → ENNReal) :
    ∫⁻ z, g (F.flow z t) = ∫⁻ z, g z := by
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (s := univ) MeasurableSet.univ
    (fun z _ => (F.label z t ht).hasFDerivWithinAt) (F.bijective t ht).1.injOn g
  simpa only [Set.image_univ,(F.bijective t ht).2.range_eq,setLIntegral_univ,
    F.det_one _ _ ht,abs_one,ENNReal.ofReal_one,one_mul] using hh.symm

lemma label_hit_tonelli {f₀ : Phase → ℝ} (hf₀ : Measurable f₀)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    (∫⁻ s : ℝ, ∫⁻ z : Phase, H.indicator
      (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2)) (s,z)) =
      ∫⁻ z : Phase, ENNReal.ofReal (f₀ z) * volume {s : ℝ | (s,z) ∈ H} := by
  have hm : Measurable (H.indicator (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2))) :=
    ((hf₀.comp measurable_snd).ennreal_ofReal).indicator hH
  rw [lintegral_lintegral_swap (f := fun s z => H.indicator
    (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2)) (s,z)) hm.aemeasurable]
  apply lintegral_congr
  intro z
  have hs : MeasurableSet {s : ℝ | (s,z) ∈ H} :=
    hH.preimage (measurable_id.prodMk measurable_const)
  calc
    _ = ∫⁻ s : ℝ, ENNReal.ofReal (f₀ z) * {s : ℝ | (s,z) ∈ H}.indicator 1 s := by
      apply lintegral_congr
      intro s
      by_cases h : (s,z) ∈ H <;> simp [Set.indicator,h]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator_one hs]

lemma PhaseFlowOn.transport_weight_lintegral {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (g : Phase → ENNReal) :
    (∫⁻ z, ENNReal.ofReal (f (t,z)) * g z) =
      ∫⁻ z, ENNReal.ofReal (f (0,z)) * g (F.flow z t) := by
  rw [← F.lintegral_comp ht (fun z => ENNReal.ofReal (f (t,z)) * g z)]
  apply lintegral_congr
  intro z
  rw [F.transport hf heq ht]

def phaseHits (α : Phase → ℝ → Phase) (T : ℝ) (H : Set (ℝ × Phase)) : Set (ℝ × Phase) :=
  {p | p.1 ∈ Ioo 0 T ∧ (p.1,α p.2 p.1) ∈ H}

lemma PhaseFlowOn.measurable_phaseHits {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    MeasurableSet (phaseHits F.flow T H) := by
  let α₀ := (Ioo 0 T ×ˢ (univ : Set Phase)).indicator (fun p : ℝ × Phase => F.flow p.2 p.1)
  have hm : Measurable (fun p : ℝ × Phase => (p.1,α₀ p)) :=
    measurable_fst.prodMk F.measurable_joint_flow_zero
  have he : phaseHits F.flow T H = (Ioo 0 T ×ˢ (univ : Set Phase)) ∩
      (fun p : ℝ × Phase => (p.1,α₀ p)) ⁻¹' H := by
    ext p
    by_cases hp : p.1 ∈ Ioo 0 T
    · simp only [phaseHits,mem_ofPred_eq,hp,true_and,mem_inter_iff,mem_prod,
        mem_univ,and_true,mem_preimage,α₀,Set.indicator_of_mem (show p ∈ Ioo 0 T ×ˢ (univ : Set Phase) from ⟨hp,mem_univ _⟩)]
    · simp only [phaseHits,mem_ofPred_eq,hp,false_and,mem_inter_iff,mem_prod,
        mem_univ,and_true]
  rw [he]
  exact (measurableSet_Ioo.prod MeasurableSet.univ).inter (hH.preimage hm)

lemma PhaseFlowOn.phase_occupation_identity {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    (∫⁻ t in Ioo 0 T, ∫⁻ z : Phase, H.indicator (fun p => ENNReal.ofReal (f p)) (t,z)) =
      labelOccupation (fun z => f (0,z)) (fun z => {t | (t,z) ∈ phaseHits F.flow T H}) := by
  have hf₀ : Measurable (fun z : Phase => f (0,z)) :=
    (hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨le_rfl,hT⟩,mem_univ _⟩)).measurable
  have hfixed (t : ℝ) (ht : t ∈ Ioo 0 T) :
      (∫⁻ z : Phase, H.indicator (fun p => ENNReal.ofReal (f p)) (t,z)) =
        ∫⁻ z : Phase, (phaseHits F.flow T H).indicator
          (fun p : ℝ × Phase => ENNReal.ofReal (f (0,p.2))) (t,z) := by
    calc
      _ = ∫⁻ z : Phase, ENNReal.ofReal (f (t,z)) * H.indicator 1 (t,z) := by
        apply lintegral_congr
        intro z
        by_cases h : (t,z) ∈ H <;> simp [Set.indicator,h]
      _ = ∫⁻ z : Phase, ENNReal.ofReal (f (0,z)) * H.indicator 1 (t,F.flow z t) :=
        F.transport_weight_lintegral hf heq (Ioo_subset_Icc_self ht) _
      _ = _ := by
        apply lintegral_congr
        intro z
        by_cases h : (t,F.flow z t) ∈ H
        · rw [Set.indicator_of_mem h,Set.indicator_of_mem
              (show (t,z) ∈ phaseHits F.flow T H from ⟨ht,h⟩)]
          simp
        · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem
              (show (t,z) ∉ phaseHits F.flow T H from fun hh => h hh.2)]
          simp
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ z : Phase, (phaseHits F.flow T H).indicator
        (fun p : ℝ × Phase => ENNReal.ofReal (f (0,p.2))) (t,z) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Ioo 0 T
      · rw [Set.indicator_of_mem ht]
        exact hfixed t ht
      · rw [Set.indicator_of_notMem ht]
        symm
        calc
          _ = ∫⁻ _z : Phase, (0 : ENNReal) := by
            apply lintegral_congr
            intro z
            exact Set.indicator_of_notMem (fun h => ht h.1) _
          _ = _ := lintegral_zero
    _ = _ := label_hit_tonelli hf₀ (F.measurable_phaseHits hH)
end RVM

end

end OAI
