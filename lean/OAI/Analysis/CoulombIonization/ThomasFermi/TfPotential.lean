import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfPowerIntegralDeriv
import OAI.Analysis.CoulombIonization.ThomasFermi.TfDilation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace CoulombAnalysis
open CoulombAtom

def tfPotential (ρ : Space → ℝ) (x : Space) : ℝ := ∫ y, ρ y / ‖x - y‖
def tfField (Z : ℝ) (ρ : Space → ℝ) (x : Space) : ℝ := Z / ‖x‖ - tfPotential ρ x

lemma tfPotential_nonneg {ρ : Space → ℝ} (hρ : ∀ᵐ y, 0 ≤ ρ y) (x : Space) :
    0 ≤ tfPotential ρ x := by
  apply integral_nonneg_of_ae
  exact hρ.mono fun y hy => div_nonneg hy (norm_nonneg _)

lemma tfPotential_extension (R : ℝ) (f : TFLp (ballMeasure R)) (x : Space) :
    tfPotential (tfExtension R f) x = tfBallPotential R f x := by
  have he : (fun y => tfExtension R f y / ‖x - y‖) =
      (ball 0 R).indicator (fun y => f y / ‖x - y‖) := by
    ext y
    by_cases hy : y ∈ ball (0 : Space) R <;> simp [tfExtension, hy]
  unfold tfPotential tfBallPotential
  rw [he]
  exact integral_indicator measurableSet_ball

lemma tf_unit_price_extension_euler {Z : ℝ} (hZ : 0 < Z)
    {f : TFLp (ballMeasure Z)} (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional Z tfKinetic Z 1 f ≤
      tfBallFunctional Z tfKinetic Z 1 g) :
    ∀ᵐ x, tfExtension Z f x =
      (max (tfField Z (tfExtension Z f) x - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ) := by
  have he := (ae_restrict_iff' measurableSet_ball).mp
    (tfBallFunctional_euler Z Z 1 tfKinetic_pos hf hmin)
  filter_upwards [he] with x hx
  by_cases hx' : x ∈ ball (0 : Space) Z
  · simp only [tfField, tfPotential_extension]
    simpa only [tfExtension, indicator_of_mem hx'] using hx hx'
  · have hr : Z ≤ ‖x‖ := le_of_not_gt (mt mem_ball_zero_iff.mpr hx')
    have hq : Z / ‖x‖ ≤ 1 := (div_le_one (hZ.trans_le hr)).mpr hr
    have hp := tfPotential_nonneg (tfExtension_nonneg hf) x
    have hfield : tfField Z (tfExtension Z f) x - 1 ≤ 0 := by unfold tfField; linarith
    rw [max_eq_right hfield]
    simp [tfExtension, hx']

theorem tf_unit_price_exists_euler (Z : ℝ) (hZ : 0 < Z) :
    ∃ M : ℝ, ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧
      (∀ M' : ℝ, ∀ σ : Space → ℝ, TFAdmissible M' σ →
        tfFunctional Z ρ + M ≤ tfFunctional Z σ + M') ∧
      ∀ᵐ x, ρ x = (max (tfField Z ρ x - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ) := by
  obtain ⟨f, hf, hmin⟩ := tfBallFunctional_exists_minimizer Z Z 1 tfKinetic_pos
  refine ⟨_, tfExtension Z f, tfExtension_admissible hf, ?_, tf_unit_price_extension_euler hZ hf hmin⟩
  intro M' σ hσ
  obtain ⟨g, hg, he⟩ := tfAdmissible_truncate hσ Z
  have hh := hmin g hg
  rw [← tfExtension_functional hf Z 1, ← tfExtension_functional hg Z 1, one_mul, one_mul,
    tfFunctional_congr_ae Z he, integral_congr_ae he] at hh
  exact hh.trans (by simpa only [hσ.2.2.1] using tfPriced_truncate_le hZ hσ)

end CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end

end OAI
