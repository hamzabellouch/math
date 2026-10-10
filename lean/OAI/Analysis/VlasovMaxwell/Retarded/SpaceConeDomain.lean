import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.PhaseHits

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

lemma PhaseFlowOn.receiver_polar_lintegral {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) {g : Vec → ENNReal} (hg : Measurable g) :
    (∫⁻ y in ball (F.flow z T).1 (T-s), g y) =
      ∫⁻ n : Sphere, ∫⁻ r in Ioo (0 : ℝ) (T-s),
        ENNReal.ofReal (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) *
          g ((F.flow z (s+r)).1-r • n.1) ∂volume ∂sphereMeasure := by
  classical
  let S := receiverRadialDomain s T
  have hS : MeasurableSet S := (isOpen_receiverRadialDomain s T).measurableSet
  let Ψ : Vec → Phase := S.indicator (fun w => F.flow z (s+‖w‖))
  have hcΨ : ContinuousOn (fun w : Vec => F.flow z (s+‖w‖)) S := by
    intro w hw
    have ht : s+‖w‖ ∈ Ioo 0 T := ⟨by linarith [hw.1,hs.1],hw.2⟩
    have hc : ContinuousAt (fun v : Vec => (s+‖v‖,z)) w :=
      (continuousAt_const.add continuousAt_id.norm).prodMk continuousAt_const
    have hh := (F.joint z (s+‖w‖) ht).continuousAt.comp (f := fun v : Vec => (s+‖v‖,z)) hc
    exact hh.continuousWithinAt
  have hmΨ : Measurable Ψ := by
    have h := hcΨ.measurable_piecewise (continuousOn_const (c := (0 : Phase))) hS
    convert h using 1
    funext w
    by_cases hw : w ∈ S <;> simp [Ψ,Set.piecewise,hw]
  let R : Vec → Vec := S.indicator (receiverRadial F.flow z s)
  have hcR : ContinuousOn (receiverRadial F.flow z s) S :=
    fun w hw => (F.receiver_differential hs.1 z hw).continuousAt.continuousWithinAt
  have hmR : Measurable R := by
    have h := hcR.measurable_piecewise (continuousOn_const (c := (0 : Vec))) hS
    convert h using 1
    funext w
    by_cases hw : w ∈ S <;> simp [R,Set.piecewise,hw]
  have hmK : Measurable (fun w : Vec => ENNReal.ofReal
      (1-dot (‖w‖⁻¹ • w) (velocity (Ψ w).2)) * g (R w)) := by
    simp only [dot_eq_inner]
    exact ((measurable_const.sub
      ((measurable_id.norm.inv.smul measurable_id).inner
        ((contDiff_velocity (k := 1)).continuous.measurable.comp hmΨ.snd))).ennreal_ofReal).mul (hg.comp hmR)
  let H : Vec → ENNReal := S.indicator
    (fun w => ENNReal.ofReal (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) *
      g (receiverRadial F.flow z s w))
  have hH : Measurable H := by
    convert hmK.indicator hS using 1
    funext w
    by_cases hw : w ∈ S <;> simp [H,Ψ,R,Set.indicator,hw]
  rw [F.receiver_lintegral hs z g,← lintegral_indicator hS]
  change (∫⁻ w, H w) = _
  rw [lintegral_polar hH]
  apply lintegral_congr
  intro n
  let k : ℝ → ENNReal := fun r => ENNReal.ofReal
    (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) * g ((F.flow z (s+r)).1-r • n.1)
  have hn : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have he : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r^2) * H (r • n.1) =
      (Iio (T-s)).indicator k r := by
    intro r hr
    have hnorm : ‖r • n.1‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
    have hd : r • n.1 ∈ S ↔ r < T-s := by
      change 0 < ‖r • n.1‖ ∧ s+‖r • n.1‖ < T ↔ _
      rw [hnorm]
      constructor
      · intro h; linarith [h.2]
      · intro h; exact ⟨hr,by linarith⟩
    by_cases h : r < T-s
    · rw [show H (r • n.1) = _ from Set.indicator_of_mem (hd.mpr h) _,
        Set.indicator_of_mem (show r ∈ Iio (T-s) from h)]
      dsimp only [k,receiverRadial]
      have hnsmul : r⁻¹ • (r • n.1)=n.1 := by
        rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (show 0<r from hr)),one_smul]
      rw [hnorm,hnsmul,ENNReal.ofReal_mul (sq_nonneg r),mul_assoc]
    · rw [show H (r • n.1) = 0 from Set.indicator_of_notMem (fun hh => h (hd.mp hh)) _,mul_zero,
        Set.indicator_of_notMem (show r ∉ Iio (T-s) from h)]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), (Iio (T-s)).indicator k r :=
      setLIntegral_congr_fun measurableSet_Ioi he
    _ = ∫⁻ r in Ioi (0 : ℝ) ∩ Iio (T-s), k r := by
      simpa only [inter_comm] using (setLIntegral_indicator (μ := (volume : Measure ℝ))
        (t := Ioi (0 : ℝ)) measurableSet_Iio k)
    _ = _ := rfl

def spaceConeDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) : Set (ℝ × Phase) :=
  {p | p.1 ∈ Ioo 0 T ∧ p.2.1 ∈ ball (α zX T).1 (T-p.1)}

def coneOccupation (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (f : Particle) (H : Set (ℝ × Phase)) : ENNReal :=
  ∫⁻ s in Ioo (0 : ℝ) T, ∫⁻ n : Sphere, ∫⁻ r in Ioo (0 : ℝ) (T-s),
    ENNReal.ofReal (r^2*(1-dot n.1 (velocity (α zX (s+r)).2))) *
      ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (f p))
        (s,((α zX (s+r)).1-r • n.1,v)) ∂volume ∂volume ∂sphereMeasure

lemma PhaseFlowOn.cone_occupation_identity {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX : Phase) {f : Particle}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase))) (heq : VlasovOn f E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
    (hsub : H ⊆ spaceConeDomain F.flow zX T) :
    coneOccupation F.flow zX T f H =
      labelOccupation (fun z => f (0,z)) (fun z => {t | (t,z) ∈ phaseHits F.flow T H}) := by
  rw [← F.phase_occupation_identity hT hf heq hH]
  unfold coneOccupation
  symm
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hfs : Continuous (fun z : Phase => f (s,z)) :=
    hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨Ioo_subset_Icc_self hs,mem_univ _⟩)
  have hm : Measurable (fun z : Phase => H.indicator (fun p => ENNReal.ofReal (f p)) (s,z)) := by
    exact hfs.measurable.ennreal_ofReal.indicator
      (hH.preimage (measurable_const.prodMk measurable_id))
  let g : Vec → ENNReal := fun y => ∫⁻ v : Vec,
    H.indicator (fun p => ENNReal.ofReal (f p)) (s,(y,v))
  have hgm : Measurable g := hm.lintegral_prod_right'
  calc
    _ = ∫⁻ y : Vec, g y := lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ y in ball (F.flow zX T).1 (T-s), g y := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ ball (F.flow zX T).1 (T-s)
      · exact (Set.indicator_of_mem hy g).symm
      · rw [Set.indicator_of_notMem hy]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro v
        have hp : (s,(y,v)) ∉ H := fun hp => hy (hsub hp).2
        exact Set.indicator_of_notMem hp (fun p => ENNReal.ofReal (f p))
    _ = _ := F.receiver_polar_lintegral (Ioo_subset_Icc_self hs) zX hgm

lemma PhaseFlowOn.phaseHits_in_branch {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX z : Phase) {H : Set (ℝ × Phase)} (hsub : H ⊆ spaceConeDomain F.flow zX T) :
    {s | (s,z) ∈ phaseHits F.flow T H} ⊆ branchDomain F.flow zX z T := by
  intro s hs
  have hh := (hsub hs.2).2
  rw [mem_ball,dist_eq_norm, norm_sub_rev] at hh
  exact ⟨hs.1,by linarith⟩

lemma PhaseFlowOn.cone_occupation_angular_bound {E B : Field} {T δ Δ a b : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0 ≤ T) (zX : Phase) {f : Particle}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase))) (heq : VlasovOn f E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
    (hsub : H ⊆ spaceConeDomain F.flow zX T) (hδ : 0 ≤ δ) (hΔ : 0 < Δ)
    (hsource : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
      δ ≤ 1-dot (branchDirection F.flow zX z T s) (velocity (F.flow z s).2))
    (hreceiver : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
      1-dot (branchDirection F.flow zX z T s)
        (velocity (F.flow zX (branchTime F.flow zX z T s)).2) ≤ Δ)
    (himage : ∀ z, branchTime F.flow zX z T '' {s | (s,z) ∈ phaseHits F.flow T H} ⊆ Icc a b) :
    ENNReal.ofReal (δ/Δ) * coneOccupation F.flow zX T f H ≤
      ENNReal.ofReal (b-a) * ∫⁻ z, ENNReal.ofReal (f (0,z)) := by
  rw [F.cone_occupation_identity hT zX hf heq hH hsub]
  apply F.label_occupation_angular_bound zX _ hδ hΔ
    (fun z => (F.measurable_phaseHits hH).preimage (measurable_id.prodMk measurable_const))
    (fun z => F.phaseHits_in_branch zX z hsub) hsource hreceiver himage

end RVM

end

end OAI
