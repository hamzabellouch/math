import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfRotate

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
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

lemma tfAdmissible_congr {M : ℝ} {ρ σ : Space → ℝ} (hρ : TFAdmissible M ρ)
    (he : ρ =ᵐ[volume] σ) : TFAdmissible M σ := by
  refine ⟨?_, hρ.2.1.congr he, (integral_congr_ae he).symm.trans hρ.2.2.1,
    hρ.2.2.2.1.congr (he.mono fun x hx => by dsimp; rw [hx]),
    hρ.2.2.2.2.1.congr (he.mono fun x hx => by dsimp; rw [hx]), ?_⟩
  · filter_upwards [hρ.1, he] with x hx hxe
    rwa [← hxe]
  · apply hρ.2.2.2.2.2.congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
      Measure.quasiMeasurePreserving_snd.ae he] with p hp hq
    simp only [directIntegrand, hp, hq]

lemma tfPotential_congr {ρ σ : Space → ℝ} (he : ρ =ᵐ[volume] σ) (x : Space) :
    tfPotential ρ x = tfPotential σ x :=
  integral_congr_ae (he.mono fun y hy => by dsimp; rw [hy])

lemma tfField_congr (Z : ℝ) {ρ σ : Space → ℝ} (he : ρ =ᵐ[volume] σ) (x : Space) :
    tfField Z ρ x = tfField Z σ x := by simp only [tfField, tfPotential_congr he]

lemma tfField_continuousAt {M Z : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ)
    {x : Space} (hx : x ≠ 0) : ContinuousAt (tfField Z ρ) x :=
  (continuousAt_const.div continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx)).sub
    (tfPotential_continuous hρ.2.1 (tfAdmissible_memLp hρ)).continuousAt

def tfEulerDensity (Z : ℝ) (ρ : Space → ℝ) (x : Space) : ℝ :=
  (max (tfField Z ρ x - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ)

lemma tfEulerDensity_nonneg (Z : ℝ) (ρ : Space → ℝ) (x : Space) :
    0 ≤ tfEulerDensity Z ρ x := by
  unfold tfEulerDensity
  exact Real.rpow_nonneg (div_nonneg (le_max_right _ _) (mul_pos (by norm_num) tfKinetic_pos).le) _

lemma tfEulerDensity_continuousAt {M Z : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ)
    {x : Space} (hx : x ≠ 0) : ContinuousAt (tfEulerDensity Z ρ) x := by
  exact (((tfField_continuousAt hρ hx).sub continuousAt_const).max continuousAt_const |>.div_const _).rpow_const (by norm_num)

lemma tfEulerDensity_support {Z : ℝ} (hZ : 0 < Z) {ρ : Space → ℝ}
    (hρ : ∀ᵐ y, 0 ≤ ρ y) {x : Space} (hx : Z ≤ ‖x‖) : tfEulerDensity Z ρ x = 0 := by
  have hp := tfPotential_nonneg hρ x
  have hn := (div_le_one (hZ.trans_le hx)).mpr hx
  have hh : tfField Z ρ x - 1 ≤ 0 := by unfold tfField; linarith
  simp only [tfEulerDensity, max_eq_right hh, zero_div, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]

theorem tf_unit_price_exists_regular (Z : ℝ) (hZ : 0 < Z) :
    ∃ M : ℝ, ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧
      (∀ M' : ℝ, ∀ σ : Space → ℝ, TFAdmissible M' σ →
        tfFunctional Z ρ + M ≤ tfFunctional Z σ + M') ∧
      (∀ x, 0 ≤ ρ x) ∧
      (∀ x, ρ x = tfEulerDensity Z ρ x) ∧
      (∀ x y, ‖x‖ = ‖y‖ → ρ x = ρ y) ∧
      (∀ x, x ≠ 0 → ContinuousAt ρ x) ∧
      (∀ x, Z ≤ ‖x‖ → ρ x = 0) := by
  obtain ⟨f, hf, hmin⟩ := tfBallFunctional_exists_minimizer Z Z 1 tfKinetic_pos
  let ρ₀ := tfExtension Z f
  let ρ := tfEulerDensity Z ρ₀
  have he : ρ₀ =ᵐ[volume] ρ := tf_unit_price_extension_euler hZ hf hmin
  have ha := tfExtension_admissible hf
  refine ⟨∫ x, ρ₀ x, ρ, tfAdmissible_congr ha he, ?_, tfEulerDensity_nonneg Z ρ₀,
    ?_, ?_, fun x hx => tfEulerDensity_continuousAt ha hx, ?_⟩
  · intro M' σ hσ
    obtain ⟨g, hg, heg⟩ := tfAdmissible_truncate hσ Z
    have hh := hmin g hg
    rw [← tfExtension_functional hf Z 1, ← tfExtension_functional hg Z 1, one_mul, one_mul,
      tfFunctional_congr_ae Z heg, integral_congr_ae heg] at hh
    rw [← tfFunctional_congr_ae Z he]
    exact hh.trans (by simpa only [hσ.2.2.1] using tfPriced_truncate_le hZ hσ)
  · intro x
    exact congrArg (fun t => (max (t - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ))
      (tfField_congr Z he x)
  · intro x y hxy
    exact congrArg (fun t => (max (t - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ))
      (tfField_extension_radial hf hmin x y hxy)
  · exact fun x hx => tfEulerDensity_support hZ (tfExtension_nonneg hf) hx

end CoulombAnalysis

open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian

end

end OAI
