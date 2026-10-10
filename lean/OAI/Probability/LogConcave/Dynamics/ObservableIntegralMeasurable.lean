import Mathlib
import OAI.Probability.LogConcave.Dynamics.StationaryPath

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {μ : Measure E} {V : E → E}

lemma StationaryPath.observableIntegral_measurable (X : StationaryPath μ V)
    {M : E → H} (hM : Continuous M) :
    Measurable (fun y => ∫t in (0:ℝ)..1,M (X.path y t)) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact (hM.measurable.comp X.measurable).stronglyMeasurable.integral_prod_left'.measurable

theorem stationaryOutput_rms (X : StationaryPath μ V)
    {M : E → H} {L : ℝ≥0} (hM : LipschitzWith L M)
    (n : ℕ) (Z : Fin (n+1) → E → E) (hmZ : ∀j,Measurable (Z j))
    {Bz Bq : ℝ} (hBz : 0 ≤ Bz)
    (hZi : ∀j,Integrable (fun y => ‖Z j y-X.path y (probabilityNodes n j)‖^2) μ)
    (hZb : ∀j,(∫y,‖Z j y-X.path y (probabilityNodes n j)‖^2 ∂μ) ≤ Bz)
    (hqi : Integrable (fun y => ‖(∫t in (0:ℝ)..1,M (X.path y t))-
      ∑j,weight (probabilityNodes n) j 0 1 • M (X.path y (probabilityNodes n j))‖^2) μ)
    (hqb : (∫y,‖(∫t in (0:ℝ)..1,M (X.path y t))-
      ∑j,weight (probabilityNodes n) j 0 1 • M (X.path y (probabilityNodes n j))‖^2 ∂μ) ≤ Bq)
    (anchor : E → H) :
    Integrable (fun y => ‖(anchor y+∑j,weight (probabilityNodes n) j 0 1 • M (Z j y))-
      (anchor y+∫t in (0:ℝ)..1,M (X.path y t))‖^2) μ ∧
    (∫y,‖(anchor y+∑j,weight (probabilityNodes n) j 0 1 • M (Z j y))-
      (anchor y+∫t in (0:ℝ)..1,M (X.path y t))‖^2 ∂μ) ≤
      2*(centeringRowBudget n:ℝ)^2*(L:ℝ)^2*Bz+2*Bq := by
  let w := fun j => weight (probabilityNodes n) j 0 1
  let e := fun j y => M (Z j y)-M (X.path y (probabilityNodes n j))
  have hem (j : Fin (n+1)) : Measurable (e j) :=
    (hM.continuous.measurable.comp (hmZ j)).sub
      (hM.continuous.measurable.comp (X.measurable_slice _))
  have heb (j : Fin (n+1)) := lipschitz_error_sq (hmZ j) (X.measurable_slice _)
    hM (hZi j) (hZb j)
  have hsum := weighted_sum_sq w e (fun j => (hem j).aestronglyMeasurable)
    (fun j => (heb j).1) (fun j => (heb j).2)
  let q := fun y => (∫t in (0:ℝ)..1,M (X.path y t))-
    ∑j,w j • M (X.path y (probabilityNodes n j))
  have hqm : Measurable q := (X.observableIntegral_measurable hM.continuous).sub
    (Finset.measurable_sum _ (fun j _ =>
      (hM.continuous.measurable.comp (X.measurable_slice _)).const_smul _))
  have hsm : Measurable (fun y => ∑j,w j • e j y) :=
    Finset.measurable_sum _ (fun j _ => (hem j).const_smul _)
  have hh := sub_sq_bound hsm.aestronglyMeasurable hqm.aestronglyMeasurable
    hsum.1 hqi hsum.2 hqb
  have hid (y : E) : (anchor y+∑j,w j • M (Z j y))-
      (anchor y+∫t in (0:ℝ)..1,M (X.path y t))=(∑j,w j • e j y)-q y := by
    simp only [e,q,smul_sub,Finset.sum_sub_distrib]
    abel
  dsimp only [w] at hid
  simp_rw [hid]
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hw := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (centeringFullWeight_bound n) 2
  have hv := mul_le_mul_of_nonneg_right hw (show 0 ≤ (L:ℝ)^2*Bz by positivity)
  change (∑j,|w j|)^2*((L:ℝ)^2*Bz) ≤ _ at hv
  nlinarith
end LogConcaveSampling

end

end

end OAI
