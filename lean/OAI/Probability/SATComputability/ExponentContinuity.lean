import OAI.Probability.DilutedSpin.FunctionalContinuity
import OAI.Probability.SATComputability.RationalExponents

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal

local instance exponentContinuityMeasurable (X : TopCat) : MeasurableSpace X := borel X
local instance exponentContinuityBorel (X : TopCat) : BorelSpace X := ⟨rfl⟩

abbrev UnitExponents (r : ℕ) := {m : Fin r → ℝ // ∀ i, 0 < m i ∧ m i < 1}

def exponentTail {r : ℕ} (m : UnitExponents (r+1)) : UnitExponents r :=
  ⟨fun i => m.val i.succ, fun i => m.property i.succ⟩

theorem exponentTail_continuous (r : ℕ) :
    Continuous (exponentTail (r := r)) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)

theorem logMean_continuous_exponents {ι : Type} [Fintype ι]
    (r : ℕ) (g : (ι → ℝ) → ℝ) (hg : Continuous g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) (eta : ι → Hierarchy r) :
    Continuous (fun m : UnitExponents r => logMean r g m.val eta) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    let (i : ι) : IsProbabilityMeasure ((eta i).toMeasure) := by
      exact (eta i : ProbabilityMeasure (Hierarchy r)).property
    have hBn : 0 ≤ B := (abs_nonneg (g (fun _ => 0))).trans (hB _)
    have hc : Continuous (fun m : UnitExponents (r+1) =>
        ∫ x : ι → Hierarchy r, Real.exp (m.val 0 * logMean r g (fun i => m.val i.succ) x)
          ∂Measure.pi (fun i => (eta i).toMeasure)) := by
      apply continuous_of_dominated (bound := fun _ => Real.exp B)
      · intro m
        exact (Real.continuous_exp.comp ((logMean_continuous_bound r g hg hB _
          (fun i => (m.property i.succ).1)).1.const_mul (m.val 0))).aestronglyMeasurable
      · intro m
        apply ae_of_all
        intro x
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hb := (logMean_continuous_bound r g hg hB _
          (fun i => (m.property i.succ).1)).2 x
        calc
          _ ≤ m.val 0 * B := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hb) (m.property 0).1.le
          _ ≤ B := by nlinarith [(m.property 0).2]
      · exact integrable_const _
      · apply ae_of_all
        intro x
        exact Real.continuous_exp.comp (((continuous_apply 0).comp continuous_subtype_val).mul
          ((ih x).comp (exponentTail_continuous r)))
    have hpos (m : UnitExponents (r+1)) :
        0 < ∫ x : ι → Hierarchy r,
          Real.exp (m.val 0 * logMean r g (fun i => m.val i.succ) x)
            ∂Measure.pi (fun i => (eta i).toMeasure) :=
      MeasureMean.exp_integral_pos _
        (logMean_continuous_bound r g hg hB _ (fun i => (m.property i.succ).1)).1.measurable
        (logMean_continuous_bound r g hg hB _ (fun i => (m.property i.succ).1)).2 _
    exact (hc.log (fun m => (hpos m).ne')).div
      ((continuous_apply 0).comp continuous_subtype_val) (fun m => (m.property 0).1.ne')

theorem trialLog_continuous_exponents {ι : Type} [Fintype ι]
    (r : ℕ) (g : (ι → ℝ) → ℝ) (hg : Continuous g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) (ζ : Hierarchy (r+1)) :
    Continuous (fun m : UnitExponents r => trialLog r ζ m.val g) := by
  let : IsProbabilityMeasure ζ.toMeasure := (ζ : ProbabilityMeasure (Hierarchy r)).property
  apply continuous_of_dominated (bound := fun _ => B)
  · intro m
    exact (logMean_continuous_bound r g hg hB m.val (fun i => (m.property i).1)).1.aestronglyMeasurable
  · intro m
    exact ae_of_all _ (fun eta => by
      simpa only [Real.norm_eq_abs] using
        (logMean_continuous_bound r g hg hB m.val (fun i => (m.property i).1)).2 eta)
  · exact integrable_const _
  · exact ae_of_all _ (logMean_continuous_exponents r g hg hB)

theorem functional_continuous_unit_exponents {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) :
    Continuous (fun m : UnitExponents r => functional M r ζ m.val) := by
  have hcfield (k : ℕ) (θ : Fin k → InteractionSample p) :
      Continuous (fun m : UnitExponents r => trialSiteField M m.val ζ θ) := by
    apply continuous_of_dominated (bound := fun h : ℝ => |h|+∑ j, ‖(θ j).1‖)
    · intro m
      exact (integrable_trial_site_field M m.val (fun i => (m.property i).1) hh ζ θ).aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun h => by
        simpa only [Real.norm_eq_abs] using (trial_site_bound r m.val (fun i => (m.property i).1) ζ θ h))
    · exact hh.add (integrable_const _)
    · exact ae_of_all _ (fun h => trialLog_continuous_exponents r _
        (continuous_siteLog θ h) (siteLog_bound θ h) ζ)
  have hcdisorder (k : ℕ) :
      Continuous (fun m : UnitExponents r => trialSiteDisorder M m.val ζ k) := by
    apply continuous_of_dominated (bound := fun θ : Fin k → InteractionSample p =>
      (∫ h : ℝ, |h| ∂M.field.toMeasure)+∑ j, ‖(θ j).1‖)
    · intro m
      exact (stronglyMeasurable_trialSiteField M m.val (fun i => (m.property i).1) ζ k).aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun θ => by
        simpa only [Real.norm_eq_abs] using (trialSiteField_bound M m.val (fun i => (m.property i).1) hh ζ θ))
    · exact (integrable_const _).add (interaction_sum_integrable M hθ k)
    · exact ae_of_all _ (hcfield k)
  have hcsite : Continuous (fun m : UnitExponents r =>
      ∫ k, trialSiteDisorder M m.val ζ k ∂poissonMeasure (M.alpha*p)) := by
    apply continuous_of_dominated (bound := fun k : ℕ =>
      (∫ h : ℝ, |h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p, ‖z.1‖ ∂M.disorder.toMeasure))
    · intro m
      exact (measurable_of_countable _).aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun k => by
        simpa only [Real.norm_eq_abs] using (trialSiteDisorder_bound M m.val (fun i => (m.property i).1) hθ hh ζ k))
    · exact (integrable_const _).add ((poisson_integrable_count _).mul_const _)
    · exact ae_of_all _ hcdisorder
  have hcedge : Continuous (fun m : UnitExponents r =>
      ∫ θ : InteractionSample p, trialLog r ζ m.val (fun x => Real.log (edge θ.1 x))
        ∂M.disorder.toMeasure) := by
    apply continuous_of_dominated (bound := fun θ : InteractionSample p => ‖θ.1‖)
    · intro m
      exact (((trial_edge_lipschitz r m.val (fun i => (m.property i).1) ζ).continuous.comp
        continuous_fst).aestronglyMeasurable)
    · intro m
      exact ae_of_all _ (fun θ => by
        simpa only [Real.norm_eq_abs] using (trial_edge_bound r m.val (fun i => (m.property i).1) ζ θ.1))
    · exact hθ
    · exact ae_of_all _ (fun θ => trialLog_continuous_exponents r _
        (continuous_log_edge θ.1) (log_edge_bound θ.1) ζ)
  exact (continuous_const.add hcsite).sub (continuous_const.mul hcedge)

theorem isOpen_unit_exponents (r : ℕ) :
    IsOpen {m : Fin r → ℝ | ∀ i, 0 < m i ∧ m i < 1} := by
  have he : {m : Fin r → ℝ | ∀ i, 0 < m i ∧ m i < 1} =
      ⋂ i : Fin r, {m | 0 < m i ∧ m i < 1} := by ext; simp
  rw [he]
  exact isOpen_iInter_of_finite (fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const))

theorem functional_continuousAt_exponents {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) {m : Fin r → ℝ} (hm : Exponents m) :
    ContinuousAt (fun m => functional M r ζ m) m := by
  have hc : ContinuousOn (fun m => functional M r ζ m)
      {m : Fin r → ℝ | ∀ i, 0 < m i ∧ m i < 1} :=
    continuousOn_iff_continuous_domRestrict.mpr
      (functional_continuous_unit_exponents M hθ hh ζ)
  exact (hc m hm.2).continuousAt ((isOpen_unit_exponents r).mem_nhds hm.2)

end FixedClauseThreshold.Computability

end OAI
