import OAI.MathematicalPhysics.Boltzmann.Approximation.CapActualLossDensity
import OAI.MathematicalPhysics.Boltzmann.Branching.HotWindowGeometry
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongCompactPairTests

namespace OAI

section

/-! # A positive-measure region reached from the fixed initial hot core -/

noncomputable section

open MeasureTheory Set Metric

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def survivalCore (ell : ℝ) : Set HotKineticPhase :=
  {z | z.1.1 ∈ Ioo (0:ℝ) (1/2) ∧
    ‖(JetBarrier.flight (-z.1.1) (z.1.2,z.2)).1‖ < ell/16 ∧
      z.2 ∈ HotSeedProfile.velocityCore}

theorem survivalCore_open (ell : ℝ) : IsOpen (survivalCore ell) := by
  have hc : Continuous (fun z : HotKineticPhase =>
      (JetBarrier.flight (-z.1.1) (z.1.2,z.2)).1) := by
    unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
    fun_prop
  exact (isOpen_Ioo.preimage continuous_fst.fst).inter
    ((isOpen_lt hc.norm continuous_const).inter
      (HotSeedProfile.velocityCore_open.preimage continuous_snd))

theorem survivalCore_nonempty {ell : ℝ} (hell : 0 < ell) : (survivalCore ell).Nonempty := by
  obtain ⟨v,hv⟩ := HotSeedProfile.velocityCore_nonempty
  let p : JetPrototype.Phase := (0,v)
  let u := JetBarrier.flight (1/4) p
  refine ⟨((1/4,u.1),u.2),?_,?_,hv⟩
  · norm_num
  · change ‖(JetBarrier.flight (-(1/4)) (JetBarrier.flight (1/4) p)).1‖ < ell/16
    rw [JetFreeTransport.neg_flight]
    simpa only [p,norm_zero] using (show (0:ℝ) < ell/16 by positivity)

theorem survivalCore_positive_measure {ell : ℝ} (hell : 0 < ell) :
    ∃ R : ℝ, (hotWindowVolume (1/2) R) (survivalCore ell) ≠ 0 := by
  obtain ⟨z,hz⟩ := survivalCore_nonempty hell
  let R := ‖z.1.2‖+1
  let o : Set HotKineticPhase := survivalCore ell ∩
    ((Ioo (0:ℝ) (1/2) ×ˢ ball (0 : JetPrototype.Space) R) ×ˢ univ)
  have hopen : IsOpen o := (survivalCore_open ell).inter
    ((isOpen_Ioo.prod isOpen_ball).prod isOpen_univ)
  have hzo : z ∈ o := ⟨hz,⟨⟨hz.1,by simp [R]⟩,mem_univ _⟩⟩
  have hpos : (volume : Measure HotKineticPhase) o ≠ 0 := hopen.measure_ne_zero volume ⟨z,hzo⟩
  refine ⟨R,?_⟩
  rw [hotWindowVolume_eq,Measure.restrict_apply (survivalCore_open ell).measurableSet]
  intro he
  apply hpos
  apply measure_mono_null _ he
  rintro x ⟨hxc,⟨⟨hxt,hxx⟩,hxv⟩⟩
  exact ⟨hxc,⟨⟨⟨hxt.1.le,hxt.2.le⟩,ball_subset_closedBall hxx⟩,hxv⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positive survival weights can be removed from each characteristic prefix -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P] {μ : Measure ℝ}

omit [MeasurableSpace P] in
theorem initialSurvival_le_twoTimeSurvival {f : ℝ × P → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : ℝ × P) (s : ℝ) : timeSurvival μ f z ≤ twoTimeSurvival μ f (z,s) := by
  have ht := timePrimitive_nonneg (μ := μ) hf z
  have hs := timePrimitive_nonneg (μ := μ) hf (s,z.2)
  apply Real.exp_le_exp.mpr
  change -timePrimitive μ f z ≤ -max 0 (timePrimitive μ f z-timePrimitive μ f (s,z.2))
  exact neg_le_neg (max_le ht (sub_le_self _ hs))

theorem survival_source_unweight {f g : ℝ × P → ℝ}
    (hf : ∀ z, 0 ≤ f z) (hgm : Measurable g) (hgn : ∀ z, 0 ≤ g z) (z : ℝ × P)
    (hi : Integrable (fun s => if s ≤ z.1 then twoTimeSurvival μ f (z,s)*g (s,z.2) else 0) μ) :
    Integrable (fun s => if s ≤ z.1 then g (s,z.2) else 0) μ := by
  have hc : 0 < timeSurvival μ f z := Real.exp_pos _
  apply (hi.div_const (timeSurvival μ f z)).mono'
    ((hgm.comp (measurable_id.prodMk measurable_const)).ite
      (measurableSet_le measurable_id measurable_const) measurable_const).aestronglyMeasurable
  filter_upwards [] with s
  change ‖if s ≤ z.1 then g (s,z.2) else 0‖ ≤
    (if s ≤ z.1 then twoTimeSurvival μ f (z,s)*g (s,z.2) else 0)/timeSurvival μ f z
  split_ifs
  · rw [Real.norm_of_nonneg (hgn (s,z.2))]
    apply (le_div_iff₀ hc).mpr
    have h := mul_le_mul_of_nonneg_right (initialSurvival_le_twoTimeSurvival (μ := μ) hf z s) (hgn (s,z.2))
    nlinarith only [h]
  · simp

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A measurable fixed positive profile on the transported seed core -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def survivalProfile (q ell c C : ℝ) (z : HotKineticPhase) : ℝ :=
  (survivalCore ell).indicator (fun z => VelocityWeight.H q z.2 *
    (Real.exp (-(C*(‖z.2‖+1))*z.1.1) * (c*(ell/2)*(HotSeedProfile.normLower q/HotSeedProfile.bound)))) z

theorem survivalProfile_measurable (q ell c C : ℝ) : Measurable (survivalProfile q ell c C) := by
  apply Measurable.indicator _ (survivalCore_open ell).measurableSet
  apply ((ChartKernel.measurable_H q).comp measurable_snd).mul
  exact ((by fun_prop : Measurable (fun z : HotKineticPhase =>
    Real.exp (-(C*(‖z.2‖+1))*z.1.1)))).mul_const _

theorem survivalProfile_nonneg {q ell c C : ℝ} (hell : 0 ≤ ell) (hc : 0 ≤ c)
    (z : HotKineticPhase) : 0 ≤ survivalProfile q ell c C z := by
  apply indicator_nonneg _ z
  intro z _
  exact mul_nonneg (VelocityWeight.H_nonneg q _) (mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg hc (by positivity))
      (div_nonneg (HotSeedProfile.normLower_pos q).le HotSeedProfile.bound_pos.le)))

theorem survivalProfile_pos {q ell c C : ℝ} (hell : 0 < ell) (hc : 0 < c)
    {z : HotKineticPhase} (hz : z ∈ survivalCore ell) : 0 < survivalProfile q ell c C z := by
  rw [survivalProfile,indicator_of_mem hz]
  exact mul_pos (VelocityWeight.H_pos q _) (mul_pos (Real.exp_pos _)
    (mul_pos (mul_pos hc (by positivity))
      (div_pos (HotSeedProfile.normLower_pos q) HotSeedProfile.bound_pos)))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
