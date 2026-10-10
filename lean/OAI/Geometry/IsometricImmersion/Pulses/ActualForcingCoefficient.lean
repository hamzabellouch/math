import OAI.Geometry.IsometricImmersion.Energy.HeightEnergy
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def forcingCoefficient (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (1 - covectorNormSq g z p) / (2 * covHessian g z p 0 0)

theorem forcingCoefficient_eq_energy {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U) :
    forcingCoefficient g z p =
      heightEnergy g z p / (2 * (g p).det * covHessian g z p 0 0) := by
  unfold forcingCoefficient heightEnergy
  have hd := metricDet_ne_zero hg hp
  by_cases hh : covHessian g z p 0 0 = 0
  · simp [hh]
  · field_simp [hd, hh]

theorem forcingCoefficient_contDiffOn {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U)
    (hxx : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (forcingCoefficient g z) S := by
  apply (contDiffOn_const.sub ((covectorNormSq_contDiffOn hg hU hz).mono hSU)).div
    (contDiffOn_const.mul ((covHessian_contDiffOn hg hU hz 0 0).mono hSU))
  intro p hp
  exact mul_ne_zero (by norm_num) (hxx p hp)

theorem forcingCoefficient_abs_eq {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    (hE : 0 ≤ heightEnergy g z p) :
    |forcingCoefficient g z p| =
      heightEnergy g z p / (2 * (g p).det * |covHessian g z p 0 0|) := by
  rw [forcingCoefficient_eq_energy hg z hp, abs_div, abs_of_nonneg hE]
  simp only [abs_mul, abs_of_pos (hg.2 p hp).det_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem forcingCoefficient_bounds {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    {e E d D c C : ℝ} (he : 0 < e) (hd : 0 < d) (hc : 0 < c)
    (hE : e ≤ heightEnergy g z p) (hEup : heightEnergy g z p ≤ E)
    (hdet : d ≤ (g p).det) (hdetup : (g p).det ≤ D)
    (hxx : c ≤ |covHessian g z p 0 0|) (hxxup : |covHessian g z p 0 0| ≤ C) :
    0 < e / (2 * D * C) ∧
      e / (2 * D * C) ≤ |forcingCoefficient g z p| ∧
      |forcingCoefficient g z p| ≤ E / (2 * d * c) := by
  have hDp : 0 < D := hd.trans_le (hdet.trans hdetup)
  have hCp : 0 < C := hc.trans_le (hxx.trans hxxup)
  have hgdet : 0 < (g p).det := hd.trans_le hdet
  have hgxx : 0 < |covHessian g z p 0 0| := hc.trans_le hxx
  have hden : 0 < 2 * (g p).det * |covHessian g z p 0 0| := by positivity
  have hdenlo : 2 * d * c ≤ 2 * (g p).det * |covHessian g z p 0 0| :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdet (by norm_num)) hxx hc.le
      (by positivity)
  have hdenup : 2 * (g p).det * |covHessian g z p 0 0| ≤ 2 * D * C :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdetup (by norm_num)) hxxup hgxx.le
      (by positivity)
  rw [forcingCoefficient_abs_eq hg hp (he.le.trans hE)]
  refine ⟨by positivity, ?_, ?_⟩
  · exact div_le_div₀ (he.le.trans hE) hE hden hdenup
  · exact div_le_div₀ (he.le.trans (hE.trans hEup)) hEup (by positivity) hdenlo

theorem forcingCoefficient_one_sign {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsPreconnected S)
    (hE : ∀ p ∈ S, 0 < heightEnergy g z p)
    (hxx : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0) :
    ∀ p ∈ S, ∀ q ∈ S, 0 < forcingCoefficient g z p * forcingCoefficient g z q := by
  have hcont := (forcingCoefficient_contDiffOn hg hz hU hSU hxx).continuousOn
  have hne (p : Coord) (hp : p ∈ S) : forcingCoefficient g z p ≠ 0 := by
    rw [forcingCoefficient_eq_energy hg z (hSU hp)]
    exact div_ne_zero (hE p hp).ne'
      (mul_ne_zero (mul_ne_zero (by norm_num) (metricDet_ne_zero hg (hSU hp))) (hxx p hp))
  intro p hp q hq
  rcases lt_or_gt_of_ne (hne p hp) with hpneg | hppos
  · have hqneg : forcingCoefficient g z q < 0 := by
      by_contra hn
      obtain ⟨b, hb, heq⟩ := hS.intermediate_value₂ hp hq hcont continuousOn_const
        hpneg.le (le_of_not_gt hn)
      exact hne b hb heq
    exact mul_pos_of_neg_of_neg hpneg hqneg
  · have hqpos : 0 < forcingCoefficient g z q := by
      by_contra hn
      obtain ⟨b, hb, heq⟩ := hS.intermediate_value₂ hq hp hcont continuousOn_const
        (le_of_not_gt hn) hppos.le
      exact hne b hb heq
    exact mul_pos hppos hqpos

end SmoothLocal.Pulse

end

end OAI
