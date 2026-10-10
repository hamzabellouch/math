import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfInfiniteFieldDominatesDilation

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
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

structure TFPriceData (Z μ : ℝ) where
  mass : ℝ
  density : TFSpace → ℝ
  admissible : TFAdmissible mass density
  minimal : ∀ M σ, TFAdmissible M σ → tfFunctional Z density + μ*mass ≤ tfFunctional Z σ + μ*M
  nonneg : ∀ x, 0 ≤ density x
  compact : ∃ R > 0, ∀ x, R ≤ ‖x‖ → density x = 0

def TFUnitData.scale {W b : ℝ} (D : TFUnitData W) (hW : 0 < W) (hb : 0 < b) :
    TFPriceData (b^3*W) (b^4) := by
  refine ⟨b^3*D.mass, tfDilation b D.density, tfDilation_admissible hb D.admissible,
    ?_, fun x => mul_nonneg (pow_nonneg hb.le _) (D.nonneg _), ?_⟩
  · intro M σ hσ
    have ha := tfDilation_admissible (inv_pos.mpr hb) hσ
    have hh := mul_le_mul_of_nonneg_left (D.minimal _ _ ha) (pow_nonneg hb.le 7)
    rw [tfDilation_functional hb W D.density D.admissible.1]
    have he : b⁻¹^3*(b^3*W) = W := by field_simp
    have hf := tfDilation_functional (inv_pos.mpr hb) (b^3*W) σ hσ.1
    rw [he] at hf
    rw [hf] at hh
    nlinarith [show b^7*(b⁻¹^7 * tfFunctional (b^3*W) σ) = tfFunctional (b^3*W) σ by field_simp,
      show b^7*(b⁻¹^3 * M) = b^4*M by field_simp]
  · refine ⟨tfSupportRadius/b, div_pos (zero_lt_one.trans tfSupportRadius_gt_one) hb, fun x hx => ?_⟩
    have hn : tfSupportRadius ≤ ‖b • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hb.le]
      nlinarith [(div_le_iff₀ hb).mp hx]
    rw [tfDilation, D.uniform_support hW _ hn, mul_zero]

def tfPriceLength (μ : ℝ) : ℝ := μ ^ (1/4:ℝ)
lemma tfPriceLength_pos {μ : ℝ} (hμ : 0 < μ) : 0 < tfPriceLength μ := Real.rpow_pos_of_pos hμ _
lemma tfPriceLength_four {μ : ℝ} (hμ : 0 < μ) : tfPriceLength μ ^ 4 = μ := by
  rw [tfPriceLength, ← Real.rpow_natCast _ 4, ← Real.rpow_mul hμ.le]
  norm_num
lemma tfPriceLength_three {μ : ℝ} (hμ : 0 < μ) : tfPriceLength μ ^ 3 = μ^(3/4:ℝ) := by
  rw [tfPriceLength, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hμ.le]
  norm_num

def tfPriceData {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) : TFPriceData Z μ := by
  let b := tfPriceLength μ
  have hb : 0 < b := tfPriceLength_pos hμ
  have hW : 0 < Z/b^3 := div_pos hZ (pow_pos hb _)
  let D := tfUnitData (Z/b^3) hW
  let S := D.scale hW hb
  refine ⟨b^3*D.mass, tfDilation b D.density, S.admissible, ?_, S.nonneg, S.compact⟩
  intro M σ hσ
  have hh := S.minimal M σ hσ
  change tfFunctional (b^3*(Z/b^3)) (tfDilation b D.density) + b^4*(b^3*D.mass) ≤
    tfFunctional (b^3*(Z/b^3)) σ + b^4*M at hh
  rwa [mul_div_cancel₀ _ (pow_pos hb 3).ne', tfPriceLength_four hμ] at hh

lemma tfPriceData_mass {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    (tfPriceData hZ hμ).mass = tfPriceLength μ ^ 3 *
      (tfUnitData (Z/tfPriceLength μ ^ 3) (div_pos hZ (pow_pos (tfPriceLength_pos hμ) _))).mass := by
  unfold tfPriceData
  rfl

lemma tfPriceData_deficit {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    Z-(tfPriceData hZ hμ).mass = μ^(3/4:ℝ)*tfUnitDeficit (Z/μ^(3/4:ℝ)) := by
  calc
    Z-(tfPriceData hZ hμ).mass = tfPriceLength μ ^ 3 * tfUnitDeficit (Z/tfPriceLength μ ^ 3) := by
      rw [tfPriceData_mass, tfUnitDeficit,
        dite_eq_left (div_pos hZ (pow_pos (tfPriceLength_pos hμ) _)), mul_sub,
        mul_div_cancel₀ _ (pow_pos (tfPriceLength_pos hμ) 3).ne']
    _ = _ := by rw [tfPriceLength_three hμ]

lemma tfPriceData_deficit_bounds {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    0 ≤ Z-(tfPriceData hZ hμ).mass ∧
      Z-(tfPriceData hZ hμ).mass ≤ TFUnitData.chargeCap 1 * μ^(3/4:ℝ) := by
  rw [tfPriceData_deficit hZ hμ]
  exact ⟨mul_nonneg (Real.rpow_nonneg hμ.le _) (tfUnitDeficit_nonneg _),
    by rw [mul_comm (TFUnitData.chargeCap 1)]; exact mul_le_mul_of_nonneg_left (tfUnitDeficit_le _) (Real.rpow_nonneg hμ.le (3/4:ℝ))⟩

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
