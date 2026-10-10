import OAI.Analysis.IrrationalRotation.Model.ContinuousConstruction
import OAI.Analysis.IrrationalRotation.Analysis.ParameterSmoothing
import OAI.Analysis.IrrationalRotation.Analysis.BackgroundTransfer
import OAI.Analysis.IrrationalRotation.Analysis.RelocationSeries

namespace OAI

open MeasureTheory Filter Function Set
open scoped ENNReal

namespace Invariant233.CircleParameterLaws

open InvariantProjection.Continuity TransferSupport

variable {θ : ℝ} {p : CircleParameterData}

theorem measurable_relocatedBlockTransfer (j : ℕ) :
    Measurable (p.relocatedBlockTransfer θ j) :=
  measurable_relocationTransfer (MeasurableEquiv.addRight (θ : Circle)) _ _ _
    (continuous_smoothBlock p θ j).measurable (fun n => (p.partition j n).measurable)

theorem measurable_continuousTransfer (d : BackgroundBumpData θ) :
    Measurable (p.continuousTransfer θ d) :=
  (BackgroundCost.measurable_backgroundTransferSum d).sub (Measurable.tsum fun n =>
    (measurable_smoothBlockTransfer p θ (n + 1)).add
      (measurable_relocatedBlockTransfer (p := p) (θ := θ) (n + 1)))

variable (hp : CircleParameterLaws θ p)
include hp

theorem ae_summable_rawBlock :
    ∀ᵐ x ∂circleMeasure, Summable (fun n : ℕ => p.rawBlock θ (n + 1) x) := by
  have hfin := hp.ae_finite_smoothing_and_relocation_support
  have hfinshift := (measurePreserving_add_right (volume : Measure Circle)
    (θ : Circle)).quasiMeasurePreserving.ae hfin
  filter_upwards [hfin, hfinshift] with x hx hxσ
  have hs : Summable (fun n : ℕ => p.smoothBlock θ (n + 1) x) :=
    summable_of_hasFiniteSupport hx.1
  have hd : Summable (fun n : ℕ => p.smoothBlockTransfer θ (n + 1) x) :=
    summable_of_hasFiniteSupport hx.2.1
  have hdσ : Summable (fun n : ℕ => p.smoothBlockTransfer θ (n + 1) (x + (θ : Circle))) :=
    summable_of_hasFiniteSupport hxσ.2.1
  apply ((hs.sub hd).add hdσ).congr
  intro n
  have h := smoothBlock_eq_add_coboundary (p := p) (θ := θ) (n + 1) x
  linarith

theorem relocatedBlock_eq_raw_add_coboundary (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    p.relocatedBlock θ j x = p.rawBlock θ j x +
      (p.smoothBlockTransfer θ j x + p.relocatedBlockTransfer θ j x) -
      (p.smoothBlockTransfer θ j (x + (θ : Circle)) +
        p.relocatedBlockTransfer θ j (x + (θ : Circle))) := by
  rw [hp.relocatedBlock_eq_add_coboundary j hj x,
    smoothBlock_eq_add_coboundary j x]
  ring

theorem continuousCost_ae_coboundary (d : BackgroundBumpData θ) :
    p.continuousCost θ d =ᵐ[circleMeasure] fun x => p.rawCost θ x + 1 +
      p.continuousTransfer θ d (x + (θ : Circle)) - p.continuousTransfer θ d x := by
  obtain ⟨b, hb, hformula, heq⟩ := assemble_continuous_coboundary
    (fun n => p.rawBlock θ (n + 1)) (fun n => p.relocatedBlock θ (n + 1))
    (fun n => p.smoothBlockTransfer θ (n + 1))
    (fun n => p.relocatedBlockTransfer θ (n + 1))
    (backgroundCost d) (backgroundTransferSum d) (fun x : Circle => x + (θ : Circle))
    (measurePreserving_add_right volume _).quasiMeasurePreserving
    (BackgroundCost.measurable_backgroundTransferSum d)
    (fun n => measurable_smoothBlockTransfer p θ (n + 1))
    (fun n => measurable_relocatedBlockTransfer (n + 1))
    hp.tsum_smoothBlockTransfer_support_ne_top hp.tsum_relocatedBlockTransfer_support_ne_top
    hp.ae_summable_rawBlock
    (fun n => Eventually.of_forall (hp.relocatedBlock_eq_raw_add_coboundary (n + 1) (by omega)))
    (BackgroundCost.backgroundCost_ae_coboundary d)
  have hbdef : b = p.continuousTransfer θ d := funext hformula
  filter_upwards [heq] with x hx
  simpa only [hbdef, CircleParameterData.continuousCost, CircleParameterData.rawCost] using hx

end Invariant233.CircleParameterLaws

end OAI
