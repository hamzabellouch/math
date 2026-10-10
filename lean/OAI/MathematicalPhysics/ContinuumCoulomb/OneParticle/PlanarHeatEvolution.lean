import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatDifferential

namespace OAI

/-! Differentiation in time of the actual heat average. The compact forcing
allows a fixed compact dominating set on every positive time neighborhood. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planarHeatAverage_flip (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ b, planarHeatKernel t (r - b) * planarForcing b := by
  unfold planarHeatAverage
  rw [← integral_sub_left_eq_self _ volume r]
  simp only [sub_sub_self]

theorem planarHeatKernel_joint_continuousAt {p : ℝ × PlanarPosition} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × PlanarPosition => planarHeatKernel q.1 q.2) p := by
  have h4 : 4 * p.1 ≠ 0 := by positivity
  have hpi : 4 * Real.pi * p.1 ≠ 0 := by positivity
  unfold planarHeatKernel
  fun_prop

theorem planarHeatTimeDerivative_joint_continuousAt {p : ℝ × PlanarPosition} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × PlanarPosition => planarHeatTimeDerivative q.1 q.2) p := by
  have h4 : 4 * p.1 ^ 2 ≠ 0 := by positivity
  have hne : p.1 ≠ 0 := hp.ne'
  unfold planarHeatTimeDerivative
  exact ((continuous_snd.norm.pow 2).continuousAt.div
      (continuous_const.mul (continuous_fst.pow 2)).continuousAt h4).sub
      (continuous_const.continuousAt.div continuous_fst.continuousAt hne) |>.mul
    (planarHeatKernel_joint_continuousAt hp)

theorem planarHeatTimeDerivative_forcing_continuous (t : ℝ) (r : PlanarPosition) :
    Continuous (fun b => planarHeatTimeDerivative t (r - b) * planarForcing b) := by
  have hg : Continuous (fun b : PlanarPosition => planarHeatTimeDerivative t (r - b)) := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  exact hg.mul planarForcing_C7.continuous

theorem planarHeatTimeDerivative_forcing_joint_continuousAt (r : PlanarPosition)
    {p : ℝ × PlanarPosition} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × PlanarPosition =>
      planarHeatTimeDerivative q.1 (r - q.2) * planarForcing q.2) p := by
  have h4 : 4 * p.1 ≠ 0 := by positivity
  have h42 : 4 * p.1 ^ 2 ≠ 0 := by positivity
  have hpi : 4 * Real.pi * p.1 ≠ 0 := by positivity
  have hne : p.1 ≠ 0 := hp.ne'
  have hcomp : ContinuousAt (fun q : ℝ × PlanarPosition => planarHeatTimeDerivative q.1 (r - q.2)) p := by
    unfold planarHeatTimeDerivative planarHeatKernel
    fun_prop
  have hf : Continuous (fun q : ℝ × PlanarPosition => planarForcing q.2) :=
    planarForcing_C7.continuous.comp continuous_snd
  exact hcomp.mul hf.continuousAt

theorem planarHeatTimeDerivative_local_bound {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    ∃ bound : PlanarPosition → ℝ, Integrable bound ∧
      ∀ b s, s ∈ Set.Ioo (t / 2) (3 * t / 2) →
        ‖planarHeatTimeDerivative s (r - b) * planarForcing b‖ ≤ bound b := by
  let S : Set (ℝ × PlanarPosition) := Set.Icc (t / 2) (3 * t / 2) ×ˢ tsupport planarForcing
  let F : ℝ × PlanarPosition → ℝ := fun p =>
    planarHeatTimeDerivative p.1 (r - p.2) * planarForcing p.2
  have hS : IsCompact S := isCompact_Icc.prod planarForcing_hasCompactSupport
  have hF : ContinuousOn F S := by
    intro p hp
    have hpos : 0 < p.1 := lt_of_lt_of_le (by linarith) hp.1.1
    exact (planarHeatTimeDerivative_forcing_joint_continuousAt r hpos).continuousWithinAt
  obtain ⟨C, hC⟩ := hS.bddAbove_image hF.norm
  let bound : PlanarPosition → ℝ := (tsupport planarForcing).indicator (fun _ => max 0 C)
  refine ⟨bound, ?_, ?_⟩
  · exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).mpr
      (integrableOn_const planarForcing_hasCompactSupport.measure_ne_top)
  · intro b s hs
    by_cases hb : b ∈ tsupport planarForcing
    · have hf : ‖F (s, b)‖ ≤ C := hC ⟨(s, b), ⟨⟨hs.1.le, hs.2.le⟩, hb⟩, rfl⟩
      simpa only [bound, Set.indicator_of_mem hb] using hf.trans (le_max_right 0 C)
    · simp only [bound, Set.indicator_of_notMem hb, image_eq_zero_of_notMem_tsupport hb,
        mul_zero, norm_zero, le_refl]

theorem planarHeatAverage_hasDerivAt {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    HasDerivAt (fun s => planarHeatAverage s r)
      (∫ b, planarHeatTimeDerivative t (r - b) * planarForcing b) t := by
  obtain ⟨bound, hbi, hb⟩ := planarHeatTimeDerivative_local_bound ht r
  have hn : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hi : Integrable (fun b => planarHeatKernel t (r - b) * planarForcing b) :=
    ((planarHeatKernel_continuous t).comp (continuous_const.sub continuous_id)
      |>.mul planarForcing_C7.continuous).integrable_of_hasCompactSupport
      planarForcing_hasCompactSupport.mul_left
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun b => planarHeatKernel s (r - b) * planarForcing b) :=
    Eventually.of_forall (fun s => ((planarHeatKernel_continuous s).comp
      (continuous_const.sub continuous_id) |>.mul planarForcing_C7.continuous).aestronglyMeasurable)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s b => planarHeatKernel s (r - b) * planarForcing b)
    (F' := fun s b => planarHeatTimeDerivative s (r - b) * planarForcing b)
    hn hmeas hi (planarHeatTimeDerivative_forcing_continuous t r).aestronglyMeasurable
    (Eventually.of_forall hb) hbi
    (Eventually.of_forall (fun b s hs => (planarHeatKernel_hasDerivAt
      (by linarith [hs.1] : 0 < s) (r - b)).mul_const (planarForcing b)))
  simpa only [← planarHeatAverage_flip] using hd.2

end ContinuumCoulomb

end

end OAI
