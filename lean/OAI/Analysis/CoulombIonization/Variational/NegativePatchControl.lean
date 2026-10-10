import Mathlib
import OAI.Analysis.CoulombIonization.Model
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchGapMeasurable

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma negative_part_le_of_oscillation {v w δ B : ℝ}
    (hδ : δ ≤ 1/2) (ho : |w-v| ≤ δ*(B+max (-v) 0)) :
    max (-v) 0 ≤ 2*max (-w) 0+2*δ*B := by
  have hn : 0 ≤ max (-v) 0 := le_max_right _ _
  have hdist : max (-v) 0 ≤ max (-w) 0+|w-v| := by
    apply max_le
    · have h1 := le_max_left (-w) 0
      have h2 := le_abs_self (w-v)
      linarith
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hδ hn
  nlinarith

lemma oscillation_negative_center_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {W σ : α → ℝ} {v δ B m : ℝ} (hδ : δ ≤ 1/2)
    (hm : 0 < m) (hσ : ∀ᵐ x ∂μ, 0 ≤ σ x) (hi : Integrable σ μ)
    (hp : Integrable (fun x => max (-W x) 0*σ x) μ)
    (hcount : m ≤ ∫ x, σ x ∂μ)
    (ho : ∀ᵐ x ∂μ, |W x-v| ≤ δ*(B+max (-v) 0)) :
    max (-v) 0 ≤ (2/m)*(∫ x, max (-W x) 0*σ x ∂μ)+2*δ*B := by
  have hN : 0 ≤ ∫ x, max (-W x) 0*σ x ∂μ :=
    integral_nonneg_of_ae (hσ.mono fun x hx => mul_nonneg (le_max_right _ _) hx)
  have hM : 0 < ∫ x, σ x ∂μ := hm.trans_le hcount
  have he : max (-v) 0*(∫ x, σ x ∂μ) ≤
      2*(∫ x, max (-W x) 0*σ x ∂μ)+(2*δ*B)*(∫ x, σ x ∂μ) := by
    rw [←integral_const_mul,←integral_const_mul,←integral_const_mul,←integral_add (hp.const_mul 2) (hi.const_mul _)]
    apply integral_mono_ae (hi.const_mul _) ((hp.const_mul 2).add (hi.const_mul _))
    filter_upwards [hσ,ho] with x hx hox
    have hh := mul_le_mul_of_nonneg_right (negative_part_le_of_oscillation hδ hox) hx
    change max (-v) 0 * σ x ≤ 2 * (max (-W x) 0 * σ x) + 2 * δ * B * σ x
    nlinarith
  have hh : max (-v) 0 ≤ 2*(∫ x, max (-W x) 0*σ x ∂μ)/(∫ x, σ x ∂μ)+2*δ*B := by
    have hd : max (-v) 0-2*δ*B ≤ 2*(∫ x, max (-W x) 0*σ x ∂μ)/(∫ x, σ x ∂μ) := by
      apply (le_div_iff₀ hM).mpr
      nlinarith
    linarith
  apply hh.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ 2*(∫ x, max (-W x) 0*σ x ∂μ)/m :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hN) hm hcount
    _ = _ := by ring

lemma tfPatchGap_negative_integrable (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (σ : TFLp (ballMeasure R)) :
    Integrable (fun z => max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z) (ballMeasure R) := by
  have hh := tfPatchGradient_eq_negative_field R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun f hf => tfPatchMinimizer_min R T hT Φ hf)
  exact (tfPatchGradient_mul_integrable R T Φ (tfPatchMinimizer R T hT Φ) σ).congr
    (hh.mono fun z hz => by dsimp only; rw [hz])

lemma tfPatchGap_negative_le (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (σ : TFLp (ballMeasure R)) :
    (∫ z, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z ∂ballMeasure R) ≤
      tfPatchGap R T hT Φ σ := by
  have hp := tfCoulombL_nonneg R (σ-tfPatchMinimizer R T hT Φ)
  dsimp [tfPatchGap]
  linarith

theorem tfPatchGap_negative_center_control (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) (W : Space → ℝ)
    (hW : ∀ᵐ z ∂ballMeasure R, W z = Φ z-tfBallPotential R (tfPatchMinimizer R T hT Φ) z)
    {q δ B m : ℝ} (hδ : δ ≤ 1/2) (hm : 0 < m)
    (hcount : m ≤ ∫ z in ball (0 : Space) q, σ z ∂ballMeasure R)
    (ho : ∀ z ∈ ball (0 : Space) q, |W z-W 0| ≤ δ*(B+max (-W 0) 0)) :
    max (-W 0) 0 ≤ (2/m)*tfPatchGap R T hT Φ σ+2*δ*B := by
  have hi : Integrable (fun z => σ z) (ballMeasure R) :=
    (Lp.memLp σ).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have he : (fun z => max (-W z) 0*σ z) =ᵐ[ballMeasure R]
      fun z => max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z :=
    hW.mono fun z hz => by dsimp only; rw [hz,neg_sub]
  have hp := (tfPatchGap_negative_integrable R T hT Φ σ).congr he.symm
  have hneg : ∀ᵐ z ∂ballMeasure R, 0 ≤ max (-W z) 0*σ z :=
    hσ.mono fun z hz => mul_nonneg (le_max_right _ _) hz
  have hh := oscillation_negative_center_integral hδ hm (ae_restrict_of_ae hσ)
    hi.integrableOn hp.integrableOn hcount
    ((ae_restrict_mem measurableSet_ball).mono fun z hz => ho z hz)
  apply hh.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2/m)
  apply (setIntegral_le_integral hp hneg).trans
  rw [integral_congr_ae he]
  exact tfPatchGap_negative_le R T hT Φ σ

end CoulombAnalysis

end

end OAI
