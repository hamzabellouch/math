import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.SpaceConeDomain

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
namespace EnergyPrefix

lemma mono {s : Solution} {T U : ℝ} (hs : EnergyPrefix s T) (hU : U ≤ T) :
    EnergyPrefix s U := by
  have hc : Icc (0 : ℝ) U ⊆ Icc 0 T := Icc_subset_Icc_right hU
  have ho : Ioo (0 : ℝ) U ⊆ Ioo 0 T := Ioo_subset_Ioo_right hU
  refine ⟨hs.f_smooth.mono (prod_mono hc Subset.rfl),
    hs.E_smooth.mono (prod_mono hc Subset.rfl),
    hs.B_smooth.mono (prod_mono hc Subset.rfl),
    fun t ht => hs.nonnegative t (hc ht),?_,?_,?_,
    fun t ht => hs.vlasov t (ho ht),fun t ht => hs.maxwell t (ho ht)⟩
  · obtain ⟨F,hF,hrep⟩ := hs.E_L2
    exact ⟨F,hF.mono hc,fun t ht => hrep t (hc ht)⟩
  · obtain ⟨F,hF,hrep⟩ := hs.B_L2
    exact ⟨F,hF.mono hc,fun t ht => hrep t (hc ht)⟩
  · obtain ⟨K,hK,hrep⟩ := hs.compact
    exact ⟨K,hK,fun t ht => hrep t (hc ht)⟩

lemma weighted_phase_integrable {s : Solution} {T t : ℝ} (hs : EnergyPrefix s T)
    (ht : t ∈ Icc 0 T) : Integrable (fun z : Phase => q z.2 * s.f (t,z)) := by
  have hfc : Continuous (fun z : Phase => s.f (t,z)) :=
    hs.f_smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht,mem_univ _⟩)
  have hc : Continuous (fun z : Phase => q z.2 * s.f (t,z)) :=
    ((contDiff_q (k := 1)).continuous.comp continuous_snd).mul hfc
  obtain ⟨K,hK,hKs⟩ := hs.compact
  apply hc.integrable_of_hasCompactSupport
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro z hz
  by_contra hnot
  apply hz
  have hz := hnot
  have hf : s.f (t,z)=0 := by
    by_contra hn
    exact hz (hKs t ht (subset_tsupport _ hn))
  change q z.2 * s.f (t,z)=0
  rw [hf,mul_zero]

lemma phase_energy_lintegral {s : Solution} {T t : ℝ} (hs : EnergyPrefix s T)
    (ht : t ∈ Icc 0 T) :
    (∫⁻ z : Phase, ENNReal.ofReal (q z.2 * s.f (t,z))) =
      ENNReal.ofReal (∫ x : Vec, particleEnergy s (t,x)) := by
  have hi := hs.weighted_phase_integrable ht
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun z => mul_nonneg (q_pos z.2).le (hs.nonnegative t ht z)))]
  congr 1
  exact integral_prod _ hi

lemma phase_energy_bound {s : Solution} {T t : ℝ} (hs : EnergyPrefix s T)
    (ht : t ∈ Icc 0 T) :
    (∫⁻ z : Phase, ENNReal.ofReal (q z.2 * s.f (t,z))) ≤
      ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  rw [hs.phase_energy_lintegral ht]
  apply ENNReal.ofReal_le_ofReal
  rw [← (hs.mono ht.2).energy_conservation ht.1]
  apply integral_mono (hs.particle_energy_integrable ht) (hs.total_energy_integrable ht)
  intro x
  change particleEnergy s (t,x) ≤ (‖s.E (t,x)‖^2+‖s.B (t,x)‖^2)/2+particleEnergy s (t,x)
  nlinarith [sq_nonneg ‖s.E (t,x)‖,sq_nonneg ‖s.B (t,x)‖]
end EnergyPrefix

lemma PhaseFlowOn.cone_occupation_energy_bound {s : Solution} {T p a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hT : 0 ≤ T) (hs : EnergyPrefix s T)
    (zX : Phase) {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
    (hsub : H ⊆ spaceConeDomain F.flow zX T) (hp : 0 ≤ p)
    (htime : ∀ t z, (t,z) ∈ H → t ∈ Icc a b)
    (hmom : ∀ t z, (t,z) ∈ H → p ≤ q z.2) :
    ENNReal.ofReal p * coneOccupation F.flow zX T s.f H ≤
      ENNReal.ofReal (b-a) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  rw [F.cone_occupation_identity hT zX hs.f_smooth hs.vlasov hH hsub,
    ← F.phase_occupation_identity hT hs.f_smooth hs.vlasov hH,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  let C := ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x))
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ENNReal.ofReal p * (∫⁻ z : Phase, H.indicator (fun x => ENNReal.ofReal (s.f x)) (t,z)) ≤
        (Icc a b).indicator (fun _ => C) t := by
    by_cases hti : t ∈ Icc a b
    · rw [Set.indicator_of_mem hti,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply le_trans (lintegral_mono (fun z => ?_)) (hs.phase_energy_bound (Ioo_subset_Icc_self ht))
      by_cases hz : (t,z) ∈ H
      · rw [Set.indicator_of_mem hz,← ENNReal.ofReal_mul hp]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (hmom t z hz) (hs.nonnegative t (Ioo_subset_Icc_self ht) z))
      · rw [Set.indicator_of_notMem hz,mul_zero]
        exact bot_le
    · rw [Set.indicator_of_notMem hti]
      have hz : (∫⁻ z : Phase, H.indicator (fun x => ENNReal.ofReal (s.f x)) (t,z))=0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro z
        exact Set.indicator_of_notMem (fun he => hti (htime t z he)) _
      rw [hz,mul_zero]
  calc
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) T, (Icc a b).indicator (fun _ => C) t :=
      lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioo hpoint)
    _ ≤ ∫⁻ t : ℝ, (Icc a b).indicator (fun _ => C) t := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = _ := by rw [lintegral_indicator measurableSet_Icc,lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]; exact mul_comm _ _
end RVM
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def arrivalDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Vec) :=
  {p | p.1 ∈ Ioo 0 T ∧ p.1+‖(α zX T).1-p.2‖<T ∧ (α zX p.1).1≠p.2}

def arrivalLabel (α : Phase → ℝ → Phase) (p : ℝ × Vec) : ℝ × Phase :=
  (p.1,inversePhase α (p.1,(p.2,0)))

def arrivalTime (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : ℝ :=
  branchTime α zX (arrivalLabel α p).2 T p.1

def arrivalRadius (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : ℝ :=
  arrivalTime α zX T p-p.1

def arrivalDirection (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : Vec :=
  (arrivalRadius α zX T p)⁻¹ • ((α zX (arrivalTime α zX T p)).1-p.2)

def arrivalVelocity (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) (p : ℝ × Vec) : Vec :=
  velocity (α zX (arrivalTime α zX T p)).2

lemma PhaseFlowOn.arrivalLabel_mem {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    arrivalLabel F.flow p ∈ jointBranchDomain F.flow zX T := by
  have h := F.flow_inversePhase (Ioo_subset_Icc_self hp.1) (p.2,0)
  change (p.1 ∈ Ioo 0 T ∧ p.1+‖(F.flow zX T).1-(F.flow _ p.1).1‖<T) ∧
    (F.flow zX p.1).1 ≠ (F.flow _ p.1).1
  change (p.1 ∈ Ioo 0 T ∧ p.1+‖(F.flow zX T).1-(F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1‖<T) ∧
    (F.flow zX p.1).1 ≠ (F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1
  rw [h]
  exact ⟨⟨hp.1,hp.2.1⟩,hp.2.2⟩

lemma PhaseFlowOn.arrivalLabel_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {p : ℝ × Vec} (hp : p.1 ∈ Ioo 0 T) : ContinuousAt (arrivalLabel F.flow) p := by
  obtain ⟨D,_,hD⟩ := F.inverse_differential hp (p.2,0)
  exact continuousAt_fst.prodMk (hD.continuousAt.comp
    (f := fun q : ℝ × Vec => (q.1,(q.2,0)))
    (continuousAt_fst.prodMk (continuousAt_snd.prodMk continuousAt_const)))

lemma PhaseFlowOn.isOpen_arrivalDomain {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) : IsOpen (arrivalDomain F.flow zX T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hX : ContinuousAt (fun q : ℝ × Vec => (F.flow zX q.1).1) p :=
    (((F.continuousOn_time zX).fst.continuousAt (Icc_mem_nhds hp.1.1 hp.1.2)).comp
      continuousAt_fst)
  have ht : ∀ᶠ q : ℝ × Vec in 𝓝 p, q.1 ∈ Ioo 0 T :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds hp.1)
  have hd : ContinuousAt (fun q : ℝ × Vec => q.1+‖(F.flow zX T).1-q.2‖) p :=
    continuousAt_fst.add (continuousAt_const.sub continuousAt_snd).norm
  have hb := hd.eventually (isOpen_Iio.mem_nhds hp.2.1)
  have hn := (hX.sub continuousAt_snd).eventually
    (isOpen_compl_singleton.mem_nhds (sub_ne_zero.mpr hp.2.2))
  filter_upwards [ht,hb,hn] with q hq hqt hqn
  exact ⟨hq,hqt,sub_ne_zero.mp hqn⟩

lemma PhaseFlowOn.arrival_time_spec {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    arrivalTime F.flow zX T p ∈ Ioo p.1 T ∧
      arrivalTime F.flow zX T p-p.1=‖(F.flow zX (arrivalTime F.flow zX T p)).1-p.2‖ := by
  have h := F.arrivalLabel_mem zX hp
  have ht := F.branch_time_mem zX (arrivalLabel F.flow p).2 h.1 h.2
  have he := (F.branch_spec zX (arrivalLabel F.flow p).2 h.1).2
  have hh := F.flow_inversePhase (Ioo_subset_Icc_self hp.1) (p.2,0)
  change _-p.1=‖_- (F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1‖ at he
  rw [hh] at he
  exact ⟨ht,he⟩

lemma PhaseFlowOn.arrivalTime_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalTime F.flow zX T) p :=
  (F.joint_branch_continuousAt zX (F.arrivalLabel_mem zX hp)).comp
    (f := arrivalLabel F.flow) (F.arrivalLabel_continuousAt hp.1)

lemma PhaseFlowOn.arrivalRadius_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalRadius F.flow zX T) p :=
  (F.arrivalTime_continuousAt zX hp).sub continuousAt_fst

lemma PhaseFlowOn.arrivalFlow_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (fun q => F.flow zX (arrivalTime F.flow zX T q)) p := by
  have ht := (F.arrival_time_spec zX hp).1
  have hti : arrivalTime F.flow zX T p ∈ Ioo 0 T := ⟨hp.1.1.trans ht.1,ht.2⟩
  exact (F.joint zX _ hti).continuousAt.comp
    (f := fun q => (arrivalTime F.flow zX T q,zX))
    ((F.arrivalTime_continuousAt zX hp).prodMk continuousAt_const)

lemma PhaseFlowOn.arrivalDirection_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalDirection F.flow zX T) p := by
  have hn : arrivalRadius F.flow zX T p ≠ 0 := ne_of_gt (sub_pos.mpr (F.arrival_time_spec zX hp).1.1)
  exact ((F.arrivalRadius_continuousAt zX hp).inv₀ hn).smul
    ((F.arrivalFlow_continuousAt zX hp).fst.sub continuousAt_snd)

lemma PhaseFlowOn.arrivalVelocity_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalVelocity F.flow zX T) p :=
  (contDiff_velocity (k := 1)).continuous.continuousAt.comp
    (f := fun q => (F.flow zX (arrivalTime F.flow zX T q)).2)
    (F.arrivalFlow_continuousAt zX hp).snd

lemma PhaseFlowOn.norm_arrivalDirection {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ‖arrivalDirection F.flow zX T p‖=1 := by
  have ht := F.arrival_time_spec zX hp
  have hr : 0 < arrivalRadius F.flow zX T p := sub_pos.mpr ht.1.1
  rw [arrivalDirection,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),← ht.2]
  exact inv_mul_cancel₀ (ne_of_gt hr)

lemma PhaseFlowOn.measurable_arrival_zero {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) : Measurable ((arrivalDomain F.flow zX T).indicator (arrivalTime F.flow zX T)) := by
  classical
  exact (show ContinuousOn _ (arrivalDomain F.flow zX T) from
    fun _ hp => (F.arrivalTime_continuousAt zX hp).continuousWithinAt).measurable_piecewise
      continuousOn_const (F.isOpen_arrivalDomain zX).measurableSet

end RVM

end

end OAI
