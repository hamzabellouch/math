import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfCenteredPrice

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
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

def actualTFCoefficient : ℝ := (3/7:ℝ)*tfResidualCharge^(-4/3:ℝ)

lemma actualTFCoefficient_pos : 0 < actualTFCoefficient :=
  mul_pos (by norm_num) (Real.rpow_pos_of_pos tfResidualCharge_pos _)

theorem tf_actual_unit_limit : Tendsto (tfIonization 1) atTop (𝓝 actualTFCoefficient) := by
  let q := tfResidualCharge
  let c := q^(-4/3:ℝ)
  have hq : 0 < q := tfResidualCharge_pos
  have hc : 0 < c := Real.rpow_pos_of_pos hq _
  have hDc : limitDeficit q c = 1 := limitDeficit_target hq
  have hLc : limitSectorEnergy q c = actualTFCoefficient := limitSectorEnergy_target hq
  have hlow : Tendsto (fun Z => tfPriceValue Z c-tfEnergy Z Z+c) atTop (𝓝 actualTFCoefficient) := by
    have hh := (tf_priced_energy_limits hc).1.add_const c
    have he : limitPriceEnergy q c+c = actualTFCoefficient := by
      rw [← hLc, ← limitPriceEnergy_add hc, hDc, mul_one]
    change Tendsto _ atTop (𝓝 (limitPriceEnergy q c+c)) at hh
    rwa [he] at hh
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_gt_atTop (1:ℝ), hlow.eventually (lt_mem_nhds ha)] with Z hZ hl
    have hh := tfPriceValue_le_energy (zero_lt_one.trans hZ) hc (by linarith : 0 ≤ Z-1)
    unfold tfIonization
    linarith
  · intro a ha
    have hcont := (continuous_limitSectorEnergy q).continuousAt (x := c)
    obtain ⟨δ, hδ, hδL⟩ := Metric.continuousAt_iff.mp hcont ((a-actualTFCoefficient)/2) (by linarith)
    let η := min (c/2) (δ/2)
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hηc : η ≤ c/2 := min_le_left _ _
    have hηδ : η < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hm : 0 < c-η := by linarith
    have hp : 0 < c+η := by linarith
    have hDm : limitDeficit q (c-η) < 1 := by
      rw [← hDc]; exact (limitDeficit_strictMonoOn hq) hm hc (by linarith)
    have hDp : 1 < limitDeficit q (c+η) := by
      rw [← hDc]; exact (limitDeficit_strictMonoOn hq) hc hp (by linarith)
    have hLm : limitSectorEnergy q (c-η) < a := by
      have hh := hδL (show dist (c-η) c < δ by simpa [Real.dist_eq, abs_of_pos hη] using hηδ)
      rw [Real.dist_eq, hLc] at hh
      have := (abs_lt.mp hh).2
      linarith
    have hLp : limitSectorEnergy q (c+η) < a := by
      have hh := hδL (show dist (c+η) c < δ by simpa [Real.dist_eq, abs_of_pos hη] using hηδ)
      rw [Real.dist_eq, hLc] at hh
      have := (abs_lt.mp hh).2
      linarith
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (tfPriceDeficit_tendsto hm).eventually (gt_mem_nhds hDm),
      (tfPriceDeficit_tendsto hp).eventually (lt_mem_nhds hDp),
      (tf_priced_energy_limits hm).2.eventually (gt_mem_nhds hLm),
      (tf_priced_energy_limits hp).2.eventually (gt_mem_nhds hLp)] with Z hZ hdm hdp hjm hjp
    exact (tfIonization_le_priced_max hZ hm hp hdm hdp).trans_lt (max_lt hjm hjp)

theorem tf_actual_characterization : TFCharacterization actualTFCoefficient :=
  tfCharacterization_of_unit_limit tf_actual_unit_limit

theorem tf_actual_coefficient_exists : ∃ a : ℝ, 0 < a ∧ TFCharacterization a :=
  ⟨actualTFCoefficient, actualTFCoefficient_pos, tf_actual_characterization⟩

end CoulombAnalysis

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators

end

end OAI
