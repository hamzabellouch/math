import OAI.Analysis.IrrationalRotation.Analysis.ContinuousConstruction
import OAI.Analysis.IrrationalRotation.Rotation.CircleBackgroundCost
import OAI.Analysis.IrrationalRotation.Rotation.AnalyticWeightBridge
import OAI.Analysis.IrrationalRotation.Analysis.NonnegativeCostIntegral
import OAI.Analysis.IrrationalRotation.Analysis.InvariantConull

namespace OAI

open MeasureTheory Filter Function Set
open scoped ENNReal Topology

namespace Invariant233.CircleParameterLaws

open InvariantProjection.Continuity

variable {θ : ℝ} {p : CircleParameterData}

theorem measurable_rawBlock (j : ℕ) : Measurable (p.rawBlock θ j) := by
  have heq : p.rawBlock θ j = fun x => p.smoothBlock θ j x -
      p.smoothBlockTransfer θ j x + p.smoothBlockTransfer θ j (x + (θ : Circle)) := by
    funext x
    have h := smoothBlock_eq_add_coboundary (p := p) (θ := θ) j x
    linarith
  rw [heq]
  exact ((continuous_smoothBlock p θ j).measurable.sub
    (measurable_smoothBlockTransfer p θ j)).add
    ((measurable_smoothBlockTransfer p θ j).comp (measurable_id.add_const (θ : Circle)))

theorem measurable_rawCost : Measurable (p.rawCost θ) :=
  Measurable.tsum (fun n => measurable_rawBlock (n + 1))

theorem measurable_continuousCost (d : BackgroundBumpData θ) :
    Measurable (p.continuousCost θ d) :=
  (BackgroundCost.measurable_backgroundCost d).add
    (Measurable.tsum (fun n => (continuous_relocatedBlock (p := p) (θ := θ) (n + 1)).measurable))

variable (hp : CircleParameterLaws θ p)
include hp

theorem continuousOn_continuousCost (d : BackgroundBumpData θ) :
    ContinuousOn (p.continuousCost θ d) ({0}ᶜ : Set Circle) :=
  (BackgroundCost.continuousOn_backgroundCost d).add hp.continuousOn_relocatedCost

theorem continuousCost_ge_half (d : BackgroundBumpData θ) (x : Circle) :
    1 / 2 ≤ p.continuousCost θ d x :=
  (BackgroundCost.backgroundCost_ge_half d x).trans
    (le_add_of_nonneg_right (hp.relocatedCost_nonneg x))

theorem tendsto_continuousCost_atTop (d : BackgroundBumpData θ) :
    Tendsto (p.continuousCost θ d) (𝓝[≠] (0 : Circle)) atTop := by
  apply tendsto_atTop_mono (fun x => le_add_of_nonneg_right (hp.relocatedCost_nonneg x))
  exact BackgroundCost.tendsto_backgroundCost_atTop d

theorem lintegral_continuousCost_eq_top (d : BackgroundBumpData θ) :
    (∫⁻ x, ENNReal.ofReal (p.continuousCost θ d x) ∂circleMeasure) = ∞ := by
  apply lintegral_cost_add_background_eq_top (p.relocatedCost θ) (backgroundCost d)
    hp.lintegral_relocatedCost_eq_top
  exact Eventually.of_forall (fun x => (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans
    (BackgroundCost.backgroundCost_ge_half d x))

theorem isContinuousCircleWeight_continuousWeight (d : BackgroundBumpData θ) :
    IsContinuousCircleWeight (p.continuousWeight θ d) := by
  classical
  have hnonneg (x : Circle) (hx : x ≠ 0) : 0 ≤ p.continuousCost θ d x :=
    (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans (hp.continuousCost_ge_half d x)
  have hcont : Continuous (p.continuousWeight θ d) :=
    continuous_exp_neg_update 0 (p.continuousCost θ d)
      (hp.continuousOn_continuousCost d) (hp.tendsto_continuousCost_atTop d)
  have hrange : ∀ x, 0 ≤ p.continuousWeight θ d x ∧ p.continuousWeight θ d x ≤ 1 :=
    exp_neg_update_mem_Icc 0 (p.continuousCost θ d) hnonneg
  have hzero : ∀ x, p.continuousWeight θ d x = 0 ↔ x = 0 :=
    exp_neg_update_eq_zero_iff 0 (p.continuousCost θ d)
  refine ⟨hcont, hrange, hzero, ?_⟩
  have hpos := ae_pos_of_nonneg_singleton_zero (p.continuousWeight θ d) 0
    (circleMeasure_singleton 0) (fun x => (hrange x).1) hzero
  apply (hasNegInfiniteLogIntegral_iff_of_ae_pos _ hpos).mpr
  exact (lintegral_neg_log_exp_neg_update circleMeasure 0 (p.continuousCost θ d)
    (circleMeasure_singleton 0)).trans (hp.lintegral_continuousCost_eq_top d)

omit hp in
theorem continuousWeight_ae_exp_neg (d : BackgroundBumpData θ) :
    p.continuousWeight θ d =ᵐ[circleMeasure] fun x => Real.exp (-p.continuousCost θ d x) := by
  have hne : ∀ᵐ x ∂circleMeasure, x ≠ (0 : Circle) := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using circleMeasure_singleton 0
  filter_upwards [hne] with x hx
  exact Function.update_of_ne hx _ _

theorem neg_log_continuousWeight_ae_coboundary (d : BackgroundBumpData θ) :
    (fun x => -Real.log (p.continuousWeight θ d x)) =ᵐ[circleMeasure] fun x =>
      p.rawCost θ x + 1 + p.continuousTransfer θ d (x + (θ : Circle)) -
        p.continuousTransfer θ d x := by
  filter_upwards [continuousWeight_ae_exp_neg (p := p) d,
    hp.continuousCost_ae_coboundary d] with x hweight hcost
  rw [hweight, Real.log_exp, neg_neg]
  exact hcost

theorem exists_continuousWeight_factor_domain (d : BackgroundBumpData θ)
    (fstar : Circle → ℝ) (hmfstar : Measurable fstar)
    (hfstar : fstar =ᵐ[circleMeasure] fun x => Real.exp (-p.rawCost θ x)) :
    ∃ s : Set Circle, MeasurableSet s ∧ circleMeasure sᶜ = 0 ∧
      (∀ n : ℤ, ((Equiv.addRight (θ : Circle)) ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ (k + 1)) x)) *
          p.continuousWeight θ d (((Equiv.addRight (θ : Circle)) ^ k) x) =
        Real.exp (-1) * fstar (((Equiv.addRight (θ : Circle)) ^ k) x) *
          Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ k) x)) := by
  exact exists_invariant_weight_coboundary_domain (MeasurableEquiv.addRight (θ : Circle))
    (measurePreserving_add_right volume _) (p.continuousCost θ d) (p.rawCost θ)
    (p.continuousTransfer θ d) (p.continuousWeight θ d) fstar
    (measurable_continuousCost d) measurable_rawCost (measurable_continuousTransfer d)
    (hp.isContinuousCircleWeight_continuousWeight d).1.measurable hmfstar
    (hp.continuousCost_ae_coboundary d) (continuousWeight_ae_exp_neg d) hfstar

theorem exists_continuous_weight_raw_coboundary (hθ : Irrational θ) :
    ∃ f b : Circle → ℝ, IsContinuousCircleWeight f ∧ Measurable b ∧
      (fun x => -Real.log (f x)) =ᵐ[circleMeasure] fun x =>
        p.rawCost θ x + 1 + b (x + (θ : Circle)) - b x := by
  obtain ⟨d⟩ := BackgroundCost.exists_backgroundBumpData θ hθ
  exact ⟨p.continuousWeight θ d, p.continuousTransfer θ d,
    hp.isContinuousCircleWeight_continuousWeight d, measurable_continuousTransfer d,
    hp.neg_log_continuousWeight_ae_coboundary d⟩

end Invariant233.CircleParameterLaws

end OAI
