import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.CutoffDrift

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
namespace ExactSLEBarrier
variable {a : ℝ} {T : ℝ≥0} {y j q : ℝ → ℝ}
lemma Evolution.logRadius_le (h : Evolution a T y j q) (ha : 0 ≤ a)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Real.log (y t)-j t ≤ Real.log (y 0)-j 0 := by
  have hc : ContinuousOn (fun t => Real.log (y t)-j t) (Icc 0 (T : ℝ)) :=
    (h.yc.log (fun u hu => (h.yp u hu).ne')).sub h.jc
  have hm : AntitoneOn (fun t => Real.log (y t)-j t) (Icc 0 (T : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (T : ℝ)) hc
      (fun u hu => (h.logRadius_deriv (interior_subset hu)).mono interior_subset)
      (fun u hu => div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (y u)]) (sq_nonneg _))
  exact hm ⟨le_rfl,T.coe_nonneg⟩ ht ht.1

 

theorem Evolution.height_barrier (h : Evolution a T y j q) (ha : 0 ≤ a)
    (δ ρ : ℝ) (hδ : 0 < δ) (_hρ : 0 < ρ) (hj0 : j 0 = 0)
    (hs : ∀ t ∈ Icc 0 (T : ℝ), δ^2 * q t ≤ (y t)^2)
    (hr : ∀ t ∈ Icc 0 (T : ℝ), Real.log ρ ≤ Real.log (y t)-j t)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Real.exp (Real.log (y 0)+(Real.log ρ-Real.log (y 0))/(2*δ^2)) ≤ y t := by
  let F : ℝ → ℝ := fun u => Real.log (y u) - (Real.log (y u)-j u)/(2*δ^2)
  have hFc : ContinuousOn F (Icc 0 (T : ℝ)) :=
    (h.yc.log (fun u hu => (h.yp u hu).ne')).sub
      (((h.yc.log (fun u hu => (h.yp u hu).ne')).sub h.jc).div_const _)
  have hFd (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
      HasDerivWithinAt F (a*((y u)^2-δ^2*q u)/(δ^2*(q u)^2)) (Icc 0 (T : ℝ)) u := by
    convert (h.logHeight_deriv hu).sub ((h.logRadius_deriv hu).div_const (2*δ^2)) using 1
    try rfl
    field_simp [hδ.ne',(h.qp u hu).ne']
    ring
  have hm : MonotoneOn F (Icc 0 (T : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (T : ℝ)) hFc
      (fun u hu => (hFd u (interior_subset hu)).mono interior_subset)
      (fun u hu => div_nonneg (mul_nonneg ha (sub_nonneg.mpr (hs u (interior_subset hu)))) (by positivity))
  have hi := hm ⟨le_rfl,T.coe_nonneg⟩ ht ht.1
  dsimp only [F] at hi
  rw [hj0,sub_zero] at hi
  have hdr := div_le_div_of_nonneg_right (hr t ht) (by positivity : 0 ≤ 2*δ^2)
  have he : Real.log (y 0)+(Real.log ρ-Real.log (y 0))/(2*δ^2) ≤ Real.log (y t) := by
    rw [sub_div]
    linarith
  simpa only [Real.exp_log (h.yp t ht)] using Real.exp_le_exp.mpr he

 

theorem Evolution.time_barrier (h : Evolution a T y j q) (ha : 0 ≤ a)
    (δ : ℝ) (hs : ∀ t ∈ Icc 0 (T : ℝ), δ^2 * q t ≤ (y t)^2)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : 2*a*δ^2*t ≤ (y 0)^2 := by
  let F : ℝ → ℝ := fun u => (y u)^2 + 2*a*δ^2*u
  have hFc : ContinuousOn F (Icc 0 (T : ℝ)) :=
    (h.yc.pow 2).add (continuousOn_const.mul continuousOn_id)
  have hFd (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
      HasDerivWithinAt F (2*a*(δ^2-(y u)^2/q u)) (Icc 0 (T : ℝ)) u := by
    convert ((h.yd u hu).pow 2).add ((hasDerivWithinAt_id u _).const_mul (2*a*δ^2)) using 1 <;> try rfl
    simp only [Nat.reduceSub,pow_one,Nat.cast_ofNat]
    ring
  have hm : AntitoneOn F (Icc 0 (T : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (T : ℝ)) hFc
      (fun u hu => (hFd u (interior_subset hu)).mono interior_subset)
      (fun u hu => mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (sub_nonpos.mpr ((le_div_iff₀ (h.qp u (interior_subset hu))).mpr (hs u (interior_subset hu)))))
  have hi := hm ⟨le_rfl,T.coe_nonneg⟩ ht ht.1
  dsimp only [F] at hi
  nlinarith [sq_nonneg (y t)]

end ExactSLEBarrier

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma localState_projection_deriv (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (b : ExactSLEGenerator.Driver) (L : State →L[ℝ] ℝ) (hL : L noise = 0)
    (T : ℝ≥0) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun u => L (localState a ε hε z u.toNNReal b))
      (L (cutoffDrift a ε (localState a ε hε z u.toNNReal b))) (Icc (0 : ℝ) T) u := by
  let V := fun t => localState a ε hε z t b
  have hVc : Continuous V := localState_continuous a ε hε z b
  have hAc : Continuous (fun u : ℝ => cutoffDrift a ε (V u.toNNReal)) :=
    (cutoffDrift_lipschitz a ε hε).continuous.comp (hVc.comp continuous_real_toNNReal)
  have hgc : Continuous (fun u : ℝ => L (cutoffDrift a ε (V u.toNNReal))) := L.continuous.comp hAc
  have he (t : ℝ≥0) : L (V t) = L (z,0) +
      ∫ u in (0 : ℝ)..(t : ℝ), L (cutoffDrift a ε (V u.toNNReal)) := by
    have h := congrArg L (localState_eq_zero a ε hε z t b)
    simp only [map_add,map_smul,hL,smul_zero,add_zero] at h
    rw [← L.intervalIntegral_comp_comm (hAc.intervalIntegrable 0 t)] at h
    exact h
  have hd := (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 u)
    hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt).const_add (L (z,0))
  apply hd.hasDerivWithinAt.congr_of_mem _ hu
  intro v hv
  simpa only [Real.coe_toNNReal _ hv.1] using he v.toNNReal

lemma Y_physicalDrift (a : ℝ) (v : State) :
    Y (physicalDrift a v) = -a*Y v/Q v := by
  simp only [Y_apply,physicalDrift,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,zero_div,zero_sub,← Q_eq]
  ring
lemma J_physicalDrift (a : ℝ) (v : State) :
    J (physicalDrift a v) = -a*(Q v-2*(Y v)^2)/(Q v)^2 := by
  simp only [J_apply,physicalDrift,Complex.div_re,Complex.neg_re,Complex.ofReal_re,
    Complex.neg_im,Complex.ofReal_im,neg_zero,zero_mul,zero_div,add_zero,map_pow,
    ← Q_eq]
  simp only [pow_two,Complex.mul_re]
  unfold Q
  simp only [X_apply,Y_apply]
  ring

lemma localState_evolution (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (b : ExactSLEGenerator.Driver) (T : ℝ≥0)
    (hy : ∀ t ≤ T, ε ≤ Y (localState a ε hε z t b)) :
    ExactSLEBarrier.Evolution a T
      (fun u => Y (localState a ε hε z u.toNNReal b))
      (fun u => J (localState a ε hε z u.toNNReal b))
      (fun u => Q (localState a ε hε z u.toNNReal b)) := by
  have hVc := (localState_continuous a ε hε z b).comp continuous_real_toNNReal
  have ht (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : u.toNNReal ≤ T :=
    (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
  have hp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : 0 < Y (localState a ε hε z u.toNNReal b) :=
    hε.trans_le (hy _ (ht u hu))
  refine ⟨(Y.continuous.comp hVc).continuousOn,(J.continuous.comp hVc).continuousOn,
    hp,fun u hu => Q_pos (hp u hu),?_,?_⟩
  · intro u hu
    have hd := localState_projection_deriv a ε hε z b Y (by simp [noise]) T u hu
    rw [cutoffDrift_eq_physical a ε _ (hy _ (ht u hu))] at hd
    exact (show HasDerivWithinAt _ (Y (physicalDrift a _)) _ _ from hd).congr_deriv (Y_physicalDrift a _)
  · intro u hu
    have hd := localState_projection_deriv a ε hε z b J (by simp [noise]) T u hu
    rw [cutoffDrift_eq_physical a ε _ (hy _ (ht u hu))] at hd
    exact (show HasDerivWithinAt _ (J (physicalDrift a _)) _ _ from hd).congr_deriv (J_physicalDrift a _)

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEHitting

noncomputable def regionMonitor (ε N ρ δ : ℝ) (v : State) : ℝ :=
  min (Y v-ε) (min (N-‖v‖) (min (physicalRadius v-ρ) (Y v-δ*‖v.1‖)))
lemma regionMonitor_continuous (ε N ρ δ : ℝ) : Continuous (regionMonitor ε N ρ δ) :=
  (Y.continuous.sub continuous_const).min ((continuous_const.sub continuous_norm).min
    ((physicalRadius_continuous.sub continuous_const).min
      (Y.continuous.sub (continuous_const.mul (continuous_fst.norm)))))
lemma regionMonitor_nonneg_iff (ε N ρ δ : ℝ) (v : State) :
    0 ≤ regionMonitor ε N ρ δ v ↔
      ε ≤ Y v ∧ ‖v‖ ≤ N ∧ ρ ≤ physicalRadius v ∧ δ*‖v.1‖ ≤ Y v := by
  simp only [regionMonitor,le_min_iff,sub_nonneg]
lemma regionMonitor_nonpos_iff (ε N ρ δ : ℝ) (v : State) :
    regionMonitor ε N ρ δ v ≤ 0 ↔
      Y v ≤ ε ∨ N ≤ ‖v‖ ∨ physicalRadius v ≤ ρ ∨ Y v ≤ δ*‖v.1‖ := by
  simp only [regionMonitor,min_le_iff,sub_nonpos]

noncomputable def regionStop (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) : ExactSLEGenerator.Driver → ℝ≥0 :=
  hittingBtwn (fun t b => regionMonitor ε N ρ δ (localState a ε hε z t b)) (Iic 0) 0 B

lemma regionStop_stopping (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) :
    IsStoppingTime rawFiltration (fun b => (regionStop a ε hε z N ρ δ B b : WithTop ℝ≥0)) := by
  exact boundedContact_stopping rawFiltration _
    (fun b => (regionMonitor_continuous ε N ρ δ).comp (localState_continuous a ε hε z b))
    (fun t => (regionMonitor_continuous ε N ρ δ).measurable.comp (localState_adapted a ε hε z t)) B

lemma regionStop_le (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    regionStop a ε hε z N ρ δ B b ≤ B := hittingBtwn_le b

lemma regionStop_safe (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (ht : t ≤ regionStop a ε hε z N ρ δ B b) :
    ε ≤ Y (localState a ε hε z t b) ∧ ‖localState a ε hε z t b‖ ≤ N ∧
      ρ ≤ physicalRadius (localState a ε hε z t b) ∧
      δ*‖(localState a ε hε z t b).1‖ ≤ Y (localState a ε hε z t b) := by
  apply (regionMonitor_nonneg_iff ε N ρ δ _).mp
  exact nonneg_before_boundedContact _
    (fun b => (regionMonitor_continuous ε N ρ δ).comp (localState_continuous a ε hε z b))
    (fun b => by simpa only [Function.comp_apply,localState_zero] using h0) B b t ht

lemma regionStop_contact (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver) (ht : regionStop a ε hε z N ρ δ B b < B) :
    let v := localState a ε hε z (regionStop a ε hε z N ρ δ B b) b
    Y v = ε ∨ ‖v‖ = N ∨ physicalRadius v = ρ ∨ Y v = δ*‖v.1‖ := by
  dsimp only
  have hsafe := regionStop_safe a ε hε z N ρ δ B h0 b _ le_rfl
  have hz := boundedContact_eq_zero _
    (fun b => (regionMonitor_continuous ε N ρ δ).comp (localState_continuous a ε hε z b))
    (fun b => by simpa only [Function.comp_apply,localState_zero] using h0) B b ht
  rcases (regionMonitor_nonpos_iff ε N ρ δ _).mp (le_of_eq hz) with h|h|h|h
  · exact Or.inl (le_antisymm h hsafe.1)
  · exact Or.inr (Or.inl (le_antisymm hsafe.2.1 h))
  · exact Or.inr (Or.inr (Or.inl (le_antisymm h hsafe.2.2.1)))
  · exact Or.inr (Or.inr (Or.inr (le_antisymm h hsafe.2.2.2)))

lemma localState_stopped_measurable (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Measurable (fun b => localState a ε hε z (S b) b) := by
  have hA : StronglyAdapted rawFiltration (localState a ε hε z) :=
    fun t => (localState_adapted a ε hε z t).stronglyMeasurable
  exact (measurable_stoppedValue (hA.isStronglyProgressive_of_continuous
    (localState_continuous a ε hε z)) hS).mono hS.measurableSpace_le le_rfl

 

lemma regionStop_green_mean (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a ε : ℝ) (ha : a ≠ 0) (hε : 0 < ε) (z : ℂ)
    (N B : ℝ≥0) (ρ δ : ℝ) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0)) :
    Integrable (fun b => physicalGreen a (localState a ε hε z (regionStop a ε hε z N ρ δ B b) b)) W ∧
    (∫ b, physicalGreen a (localState a ε hε z (regionStop a ε hε z N ρ δ B b) b) ∂W) = physicalGreen a (z,0) := by
  let S := regionStop a ε hε z N ρ δ B
  have hS := regionStop_stopping a ε hε z N ρ δ B
  have he (b : ExactSLEGenerator.Driver) :
      greenCutoff a ε N (localState a ε hε z (S b) b) =
      physicalGreen a (localState a ε hε z (S b) b) := by
    have hs := regionStop_safe a ε hε z N ρ δ B h0 b (S b) le_rfl
    exact (greenCutoff_eq_near a ε hε N _ hs.2.1 hs.1).eq_of_nhds
  constructor
  · have hm : Measurable (fun b => greenCutoff a ε N (localState a ε hε z (S b) b)) :=
      (greenCutoff_smooth a ε hε N).continuous.measurable.comp (localState_stopped_measurable a ε hε z S hS)
    obtain ⟨C,hC⟩ := (greenCutoff_compact a ε N).exists_bound_of_continuous
      (greenCutoff_smooth a ε hε N).continuous
    have hi : Integrable (fun b => greenCutoff a ε N (localState a ε hε z (S b) b)) W := Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall fun b => hC _)
    simpa only [he] using hi
  · have ho := localGreen_optional W hW a ε ha hε z N B (fun _ => 0) S
      (isStoppingTime_const rawFiltration 0) hS (fun _ => bot_le)
      (regionStop_le a ε hε z N ρ δ B)
      (fun b t ht => ⟨(regionStop_safe a ε hε z N ρ δ B h0 b t ht).1,
        (regionStop_safe a ε hε z N ρ δ B h0 b t ht).2.1⟩)
      univ MeasurableSet.univ
    simpa only [localState_zero,Measure.restrict_univ,integral_const,probReal_univ,one_smul] using ho.symm

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

noncomputable def heightFloor (y0 ρ δ : ℝ) : ℝ :=
  Real.exp (Real.log y0+(Real.log ρ-Real.log y0)/(2*δ^2))
noncomputable def logCeiling (y0 ρ δ : ℝ) : ℝ :=
  |Real.log (heightFloor y0 ρ δ)| + 2*|Real.log y0| + |Real.log ρ|

lemma heightFloor_pos (y0 ρ δ : ℝ) : 0 < heightFloor y0 ρ δ := Real.exp_pos _
lemma logCeiling_nonneg (y0 ρ δ : ℝ) : 0 ≤ logCeiling y0 ρ δ := by
  unfold logCeiling
  positivity

lemma heightFloor_le {y0 ρ δ : ℝ} (hy0 : 0 < y0) (hρ : 0 < ρ) (hr : ρ ≤ y0) :
    heightFloor y0 ρ δ ≤ y0 := by
  calc
    heightFloor y0 ρ δ ≤ Real.exp (Real.log y0) := ?_
    _ = y0 := Real.exp_log hy0
  unfold heightFloor
  apply Real.exp_le_exp.mpr
  have he := Real.log_le_log hρ hr
  have hd : (Real.log ρ-Real.log y0)/(2*δ^2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he) (by positivity)
  linarith

 

lemma regionStop_barriers (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (B : ℝ≥0)
    (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (ht : t ≤ regionStop a ε hε z N ρ δ B b) :
    heightFloor z.im ρ δ ≤ Y (localState a ε hε z t b) ∧
      Y (localState a ε hε z t b) ≤ z.im ∧
      |J (localState a ε hε z t b)| ≤ logCeiling z.im ρ δ ∧
      ‖localState a ε hε z t b‖ ≤ z.im/δ + logCeiling z.im ρ δ ∧
      2*a*δ^2*(t : ℝ) ≤ z.im^2 := by
  let T := regionStop a ε hε z N ρ δ B b
  let V := fun u => localState a ε hε z u b
  have hsafe (u : ℝ≥0) (hu : u ≤ T) := regionStop_safe a ε hε z N ρ δ B h0 b u hu
  have he := localState_evolution a ε hε z b T (fun u hu => (hsafe u hu).1)
  have hg : ∀ u ∈ Icc (0 : ℝ) T, δ^2 * Q (V u.toNNReal) ≤ (Y (V u.toNNReal))^2 := by
    intro u hu
    have hut : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
    have hs := (hsafe _ hut).2.2.2
    have hh := pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg _)) hs 2
    simpa only [Q_eq,Complex.normSq_eq_norm_sq,mul_pow] using hh
  have hr : ∀ u ∈ Icc (0 : ℝ) T, Real.log ρ ≤ Real.log (Y (V u.toNNReal))-J (V u.toNNReal) := by
    intro u hu
    have hut : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
    have hs := hsafe _ hut
    have hh := Real.log_le_log hρ hs.2.2.1
    have hyp : 0 < Y (V u.toNNReal) := hε.trans_le hs.1
    change Real.log ρ ≤ Real.log (physicalRadius (V u.toNNReal)) at hh
    rw [physicalRadius,Real.log_mul hyp.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
    simpa only [sub_eq_add_neg] using hh
  have hj0 : J (V (0 : ℝ).toNNReal) = 0 := by simp [V,localState_zero]
  have hym : heightFloor z.im ρ δ ≤ Y (V t) := by
    have hh := he.height_barrier ha δ ρ hδ hρ hj0 hg hr t ⟨t.coe_nonneg,ht⟩
    simpa only [Real.toNNReal_coe,Real.toNNReal_zero,localState_zero,Y_apply,heightFloor] using hh
  have hyM : Y (V t) ≤ z.im := by
    have hh := he.height_le ha t ⟨t.coe_nonneg,ht⟩
    simpa only [Real.toNNReal_coe,Real.toNNReal_zero,localState_zero,Y_apply] using hh
  have hy0 : 0 < z.im := by
    have hs := (regionMonitor_nonneg_iff ε N ρ δ (z,0)).mp h0
    exact hε.trans_le hs.1
  have htpos : 0 < Y (V t) := (heightFloor_pos _ _ _).trans_le hym
  have hlr := hr t ⟨t.coe_nonneg,ht⟩
  have hLR : Real.log (Y (V t))-J (V t) ≤ Real.log z.im := by
    have hh := he.logRadius_le ha t ⟨t.coe_nonneg,ht⟩
    simpa only [Real.toNNReal_coe,Real.toNNReal_zero,localState_zero,Y_apply,J_apply,sub_zero] using hh
  simp only [Real.toNNReal_coe] at hlr
  have hlY := Real.log_le_log htpos hyM
  have hly := Real.log_le_log (heightFloor_pos z.im ρ δ) hym
  have hj : |J (V t)| ≤ logCeiling z.im ρ δ := by
    apply abs_le.mpr
    unfold logCeiling
    constructor <;> linarith [le_abs_self (Real.log z.im),neg_le_abs (Real.log z.im),
      le_abs_self (Real.log ρ),neg_le_abs (Real.log ρ),
      le_abs_self (Real.log (heightFloor z.im ρ δ)),neg_le_abs (Real.log (heightFloor z.im ρ δ)),
      abs_nonneg (Real.log z.im),abs_nonneg (Real.log ρ),abs_nonneg (Real.log (heightFloor z.im ρ δ))]
  have hv : ‖V t‖ ≤ z.im/δ+logCeiling z.im ρ δ := by
    have hzn : ‖(V t).1‖ ≤ z.im/δ := (le_div_iff₀ hδ).mpr (by
      rw [mul_comm]
      exact (hsafe t ht).2.2.2.trans hyM)
    change max ‖(V t).1‖ ‖(V t).2‖ ≤ _
    apply max_le
    · linarith [logCeiling_nonneg z.im ρ δ]
    · change |J (V t)| ≤ _
      linarith [div_pos hy0 hδ]
  have htime : 2*a*δ^2*(t : ℝ) ≤ z.im^2 := by
    have hh := he.time_barrier ha δ hg t ⟨t.coe_nonneg,ht⟩
    simpa only [Real.toNNReal_zero,localState_zero,Y_apply] using hh
  exact ⟨hym,hyM,hj,hv,htime⟩

 

lemma regionStop_true_exit (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (B : ℝ≥0)
    (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (hεm : ε < heightFloor z.im ρ δ)
    (hN : z.im/δ+logCeiling z.im ρ δ < N)
    (hB : z.im^2 < 2*a*δ^2*(B : ℝ)) (b : ExactSLEGenerator.Driver) :
    let v := localState a ε hε z (regionStop a ε hε z N ρ δ B b) b
    physicalRadius v = ρ ∨ Y v = δ*‖v.1‖ := by
  let T := regionStop a ε hε z N ρ δ B b
  have hs := regionStop_barriers a ε ha.le hε z N ρ δ hρ hδ B h0 b T le_rfl
  have hTB : T < B := by
    have hc : 0 < 2*a*δ^2 := by positivity
    exact_mod_cast (show (T : ℝ) < B by nlinarith)
  have hc := regionStop_contact a ε hε z N ρ δ B h0 b hTB
  rcases hc with h|h|h|h
  · exfalso
    have hh := hs.1
    rw [h] at hh
    exact (not_le.mpr hεm) hh
  · exfalso
    have hh := hs.2.2.2.1
    rw [h] at hh
    exact (not_le.mpr hN) hh
  · exact Or.inl h
  · exact Or.inr h

lemma regionStop_loewner (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver) :
    let T := regionStop a ε hε z N ρ δ B b
    alive a b.1 T z ∧
      (∀ t ≤ T, loewnerMap a b.1 t z - (b.1 t : ℂ) = (localState a ε hε z t b).1) ∧
      Real.log ‖deriv (loewnerMap a b.1 T) z‖ = (localState a ε hε z T b).2 := by
  exact state_eq_loewner_on_safe a ε hε b.1 b.1.continuous b.2 z _
    (localState_continuous a ε hε z b) (fun t => localState_eq_zero a ε hε z t b) _
    (fun t ht => (regionStop_safe a ε hε z N ρ δ B h0 b t ht).1)

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

 

noncomputable def actualState (a : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : State :=
  (loewnerMap a b t z - (b t : ℂ), Real.log ‖deriv (loewnerMap a b t) z‖)
noncomputable def radialTime (a : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ t : ℝ≥0, u = t ∧ alive a b t z ∧ physicalRadius (actualState a b t z) = ρ}
noncomputable def radialWeight (a : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (ρ : ℝ) : ℝ :=
  if radialTime a b z ρ = ∞ then 0 else
    physicalGreen a (actualState a b (radialTime a b z ρ).toNNReal z)

lemma regionStop_actualState (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (ht : t ≤ regionStop a ε hε z N ρ δ B b) :
    alive a b.1 t z ∧ actualState a b.1 t z = localState a ε hε z t b := by
  have h := state_eq_loewner_on_safe a ε hε b.1 b.1.continuous b.2 z _
    (localState_continuous a ε hε z b) (fun u => localState_eq_zero a ε hε z u b) t
    (fun u hu => (regionStop_safe a ε hε z N ρ δ B h0 b u (hu.trans ht)).1)
  exact ⟨h.1, Prod.ext (h.2.1 t le_rfl) h.2.2⟩

lemma regionStop_le_hit (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (ht : physicalRadius (actualState a b.1 t z) = ρ) :
    regionStop a ε hε z N ρ δ B b ≤ t := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have he := (regionStop_actualState a ε hε z N ρ δ B h0 b t hlt.le).2
  have hc : regionMonitor ε N ρ δ (localState a ε hε z t b) ≤ 0 := by
    apply (regionMonitor_nonpos_iff _ _ _ _ _).mpr
    exact Or.inr (Or.inr (Or.inl (by simpa only [← he,ht] using (le_rfl : ρ ≤ ρ))))
  exact hn (hittingBtwn_le_of_mem bot_le
    (hlt.le.trans (regionStop_le a ε hε z N ρ δ B b)) hc)

lemma regionStop_eq_radialTime (a ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (N ρ δ : ℝ) (B : ℝ≥0) (h0 : 0 ≤ regionMonitor ε N ρ δ (z,0))
    (b : ExactSLEGenerator.Driver)
    (hr : physicalRadius (localState a ε hε z (regionStop a ε hε z N ρ δ B b) b) = ρ) :
    radialTime a b.1 z ρ = (regionStop a ε hε z N ρ δ B b : ℝ≥0∞) := by
  let T := regionStop a ε hε z N ρ δ B b
  have he := regionStop_actualState a ε hε z N ρ δ B h0 b T le_rfl
  apply le_antisymm
  · exact sInf_le ⟨T,rfl,he.1,by simpa only [he.2] using hr⟩
  · apply le_sInf
    rintro u ⟨t,rfl,_,ht⟩
    exact ENNReal.coe_le_coe.mpr (regionStop_le_hit a ε hε z N ρ δ B h0 b t ht)

lemma radialTime_top_of_no_hit (a : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (ρ : ℝ)
    (h : ¬ ∃ t : ℝ≥0, alive a b t z ∧ physicalRadius (actualState a b t z) = ρ) :
    radialTime a b z ρ = ∞ := by
  have he : {u : ℝ≥0∞ | ∃ t : ℝ≥0, u = t ∧ alive a b t z ∧ physicalRadius (actualState a b t z) = ρ} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro u ⟨t,_,ht⟩
    exact h ⟨t,ht⟩
  simp only [radialTime,he,sInf_empty]

end ExactSLEGreen
end

end OAI
