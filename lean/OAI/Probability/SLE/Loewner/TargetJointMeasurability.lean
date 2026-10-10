import OAI.Probability.SLE.Angle.TargetPotentialMeasurability
import OAI.Probability.SLE.Angle.TargetDiskRadius

namespace OAI

/-! Joint measurability in the initial disk angle. The potential is needed
only on the open angle interval, where the exact initial disk radius is
`1 - ‖x‖²`; this avoids imposing any regularity at degenerate disk charts. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma measurable_diskMapInv_joint :
    Measurable (fun q : ℝ × ℂ => diskMapInv q.1 q.2) := by
  unfold diskMapInv
  fun_prop

private lemma measurable_joint_clockIntegrand (κ : ℝ) :
    Measurable (fun q : (ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ =>
      (flow κ q.1.2.2.1 (diskMapInv q.1.2.1 q.1.2.2.2) q.2.toNNReal).im ^ 2 /
        ‖flow κ q.1.2.2.1 (diskMapInv q.1.2.1 q.1.2.2.2) q.2.toNNReal -
          (driverValue q.1.2.2.1 q.2 : ℂ)‖ ^ 4) := by
  have hz : Measurable (fun q : (ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ =>
      diskMapInv q.1.2.1 q.1.2.2.2) :=
    @Measurable.comp ((ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ) (ℝ × ℂ) ℂ
      inferInstance inferInstance inferInstance (fun q => diskMapInv q.1 q.2)
      (fun q => (q.1.2.1,q.1.2.2.2)) measurable_diskMapInv_joint
      (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd.snd)
  have hp : Measurable (fun q : (ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ =>
      (q.2.toNNReal,(q.1.2.2.1,diskMapInv q.1.2.1 q.1.2.2.2))) :=
    (continuous_real_toNNReal.measurable.comp measurable_snd).prodMk
      (measurable_fst.snd.snd.fst.prodMk hz)
  have hF : Measurable (fun q : (ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ =>
      flow κ q.1.2.2.1 (diskMapInv q.1.2.1 q.1.2.2.2) q.2.toNNReal) :=
    @Measurable.comp ((ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ) (ℝ≥0 × (Driver × ℂ)) ℂ
      inferInstance inferInstance inferInstance (fun q => flow κ q.2.1 q.2.2 q.1)
      (fun q => (q.2.toNNReal,(q.1.2.2.1,diskMapInv q.1.2.1 q.1.2.2.2)))
      (measurable_flow κ) hp
  have hB : Measurable (fun q : (ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ =>
      driverValue q.1.2.2.1 q.2) :=
    continuous_eval.measurable.comp (measurable_fst.snd.snd.fst.prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))
  exact ((Complex.measurable_im.comp hF).pow_const 2).div
    ((hF.sub hB.complex_ofReal).norm.pow_const 4)

lemma measurable_clock_joint (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      clock κ q.2.1 q.2.2.1 q.2.2.2 q.1) := by
  let A : Set ((ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ) :=
    {q | 0 ≤ q.2 ∧ q.2 ≤ (q.1.1 : ℝ)}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst.coe_nnreal_real)
  have hm : StronglyMeasurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) => ∫ u : ℝ,
      A.indicator (fun p : (ℝ≥0 × (ℝ × (Driver × ℂ))) × ℝ =>
        (flow κ p.1.2.2.1 (diskMapInv p.1.2.1 p.1.2.2.2) p.2.toNNReal).im ^ 2 /
          ‖flow κ p.1.2.2.1 (diskMapInv p.1.2.1 p.1.2.2.2) p.2.toNNReal -
            (driverValue p.1.2.2.1 p.2 : ℂ)‖ ^ 4) (q,u)) :=
    ((measurable_joint_clockIntegrand κ).indicator hA).stronglyMeasurable.integral_prod_right'
  convert hm.measurable using 1
  funext q
  rw [clock,← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Icc 0 (q.1 : ℝ)
  · have hu' : (q,u) ∈ A := hu
    simp only [indicator_of_mem hu,indicator_of_mem hu']
    simp only [Real.toNNReal_of_nonneg hu.1,NNReal.coe_mk,centeredFlow]
  · have hu' : (q,u) ∉ A := hu
    simp only [indicator_of_notMem hu,indicator_of_notMem hu']

lemma measurable_angle_joint (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      angle κ q.2.1 q.2.2.1 q.2.2.2 q.1) := by
  have hz : Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      diskMapInv q.2.1 q.2.2.2) :=
    @Measurable.comp (ℝ≥0 × (ℝ × (Driver × ℂ))) (ℝ × ℂ) ℂ
      inferInstance inferInstance inferInstance (fun q => diskMapInv q.1 q.2)
      (fun q => (q.2.1,q.2.2.2)) measurable_diskMapInv_joint
      (measurable_snd.fst.prodMk measurable_snd.snd.snd)
  have hp : Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      (q.1,(q.2.2.1,diskMapInv q.2.1 q.2.2.2))) :=
    measurable_fst.prodMk (measurable_snd.snd.fst.prodMk hz)
  have hF : Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      flow κ q.2.2.1 (diskMapInv q.2.1 q.2.2.2) q.1) :=
    @Measurable.comp (ℝ≥0 × (ℝ × (Driver × ℂ))) (ℝ≥0 × (Driver × ℂ)) ℂ
      inferInstance inferInstance inferInstance (fun q => flow κ q.2.1 q.2.2 q.1)
      (fun q => (q.1,(q.2.2.1,diskMapInv q.2.1 q.2.2.2))) (measurable_flow κ) hp
  have hB : Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      driverValue q.2.2.1 q.1) := by
    simpa only [driverValue,Real.toNNReal_coe,Function.comp_def] using
      (continuous_eval.measurable.comp (measurable_snd.snd.fst.prodMk measurable_fst) :
        Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) => q.2.2.1 q.1))
  exact (hF.sub hB.complex_ofReal).carg

lemma measurableSet_disk_surviving_joint (κ : ℝ) :
    MeasurableSet {q : ℝ≥0 × (ℝ × (Driver × ℂ)) |
      Surviving κ q.2.2.1 (diskMapInv q.2.1 q.2.2.2) q.1} := by
  have hz : Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      diskMapInv q.2.1 q.2.2.2) :=
    @Measurable.comp (ℝ≥0 × (ℝ × (Driver × ℂ))) (ℝ × ℂ) ℂ
      inferInstance inferInstance inferInstance (fun q => diskMapInv q.1 q.2)
      (fun q => (q.2.1,q.2.2.2)) measurable_diskMapInv_joint
      (measurable_snd.fst.prodMk measurable_snd.snd.snd)
  have hp : Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      (q.1,(q.2.2.1,diskMapInv q.2.1 q.2.2.2))) :=
    measurable_fst.prodMk (measurable_snd.snd.fst.prodMk hz)
  exact hp (measurableSet_surviving κ)

private def diskGreenFormula (κ θ : ℝ) (b : Driver) (x : ℂ) (t : ℝ≥0) : ℝ :=
  if Surviving κ b (diskMapInv θ x) t then
    ((1-‖x‖^2)*Real.exp (-2*a κ*clock κ θ b x t))^(-α κ) *
      Real.sin (angle κ θ b x t)^p κ
  else 0

private lemma measurable_diskGreenFormula (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      diskGreenFormula κ q.2.1 q.2.2.1 q.2.2.2 q.1) := by
  have hR : Measurable (fun q : ℝ≥0 × (ℝ × (Driver × ℂ)) =>
      (1-‖q.2.2.2‖^2)*Real.exp (-2*a κ*clock κ q.2.1 q.2.2.1 q.2.2.2 q.1)) :=
    (measurable_const.sub (measurable_snd.snd.snd.norm.pow_const 2)).mul
      ((measurable_const.mul (measurable_clock_joint κ)).exp)
  exact ((hR.pow_const (-α κ)).mul
    ((measurable_angle_joint κ).sin.pow_const (p κ))).ite
      (measurableSet_disk_surviving_joint κ) measurable_const

private lemma diskGreenFormula_eq {κ θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (b : Driver) {x : ℂ} (hx : x ∈ diskK) (t : ℝ≥0) :
    diskGreenFormula κ θ b x t=green κ θ b x t := by
  have hx1 : x ∈ ball (0:ℂ) 1 :=
    (closedBall_subset_ball (by norm_num : (1:ℝ)/4<1)) hx
  simp only [diskGreenFormula,green,radius,initialRadius_disk hθ hx1]

private lemma measurable_diskPotentialFormula (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × (ℝ × Driver) =>
      ∫⁻ x in diskK, ENNReal.ofReal (diskGreenFormula κ q.2.1 q.2.2 x q.1)) := by
  have hp : Measurable (fun q : (ℝ≥0 × (ℝ × Driver)) × ℂ =>
      (q.1.1,(q.1.2.1,(q.1.2.2,q.2)))) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.prodMk measurable_snd))
  have hm : Measurable (fun q : (ℝ≥0 × (ℝ × Driver)) × ℂ =>
      ENNReal.ofReal (diskGreenFormula κ q.1.2.1 q.1.2.2 q.2 q.1.1)) :=
    ((measurable_diskGreenFormula κ).comp hp).ennreal_ofReal
  exact @Measurable.lintegral_prod_right' _ _ _ _ (volume.restrict diskK) _ _ hm

lemma measurable_potential_angle (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × ({θ : ℝ // θ ∈ Ioo (0:ℝ) Real.pi} × Driver) =>
      potential κ q.2.1 q.2.2 q.1) := by
  have hp : Measurable (fun q : ℝ≥0 × ({θ : ℝ // θ ∈ Ioo (0:ℝ) Real.pi} × Driver) =>
      (q.1,((q.2.1:ℝ),q.2.2))) :=
    measurable_fst.prodMk ((measurable_subtype_coe.comp measurable_snd.fst).prodMk
      measurable_snd.snd)
  convert (measurable_diskPotentialFormula κ).comp hp using 1
  funext q
  apply setLIntegral_congr_fun (isClosed_closedBall.measurableSet)
  intro x hx
  exact congrArg ENNReal.ofReal (diskGreenFormula_eq q.2.1.property q.2.2 hx q.1).symm

lemma measurable_potential_restricted_angle (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × (ℝ × Driver) =>
      if q.2.1 ∈ Ioo (0:ℝ) Real.pi then potential κ q.2.1 q.2.2 q.1 else 0) := by
  classical
  have hA : MeasurableSet {q : ℝ≥0 × (ℝ × Driver) | q.2.1 ∈ Ioo (0:ℝ) Real.pi} :=
    measurable_snd.fst measurableSet_Ioo
  have hm : Measurable (fun q : ℝ≥0 × (ℝ × Driver) =>
      if q.2.1 ∈ Ioo (0:ℝ) Real.pi then
        ∫⁻ x in diskK, ENNReal.ofReal (diskGreenFormula κ q.2.1 q.2.2 x q.1)
      else (0:ℝ≥0∞)) :=
    (measurable_diskPotentialFormula κ).ite hA measurable_const
  convert hm using 1
  funext q
  by_cases hq : q.2.1 ∈ Ioo (0:ℝ) Real.pi
  · simp only [ite_eq_left hq]
    apply setLIntegral_congr_fun isClosed_closedBall.measurableSet
    intro x hx
    exact congrArg ENNReal.ofReal (diskGreenFormula_eq hq q.2.2 hx q.1).symm
  · simp only [ite_eq_right hq]

end SLEExactGauge.Target

end

end OAI
