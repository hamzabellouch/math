import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.SmallScaleRieszPacking

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def smallRieszRadiusFraction (n : ℕ) (G J v : ℝ) : ℝ :=
  min (1 / (2 * J)) (v / (2 * (oscillationTailConstant n G J + 1)))

theorem smallRieszRadiusFraction_pos (n : ℕ) (G J v : ℝ)
    (hG : 0 ≤ G) (hJ : 0 < J) (hv : 0 < v) :
    0 < smallRieszRadiusFraction n G J v := by
  unfold smallRieszRadiusFraction
  have hK := oscillationTailConstant_nonneg n G J hG hJ.le
  positivity

theorem smallRieszRadiusFraction_bounds (n : ℕ) (G J v r R : ℝ)
    (hG : 0 ≤ G) (hJ : 0 < J) (hr : 0 < r) (hR : 0 < R)
    (hsmall : r ≤ smallRieszRadiusFraction n G J v * R) :
    2 * (J * r) ≤ R ∧ oscillationTailConstant n G J * (r / R) ≤ v / 2 := by
  have hK := oscillationTailConstant_nonneg n G J hG hJ.le
  have hq : r / R ≤ smallRieszRadiusFraction n G J v := (div_le_iff₀ hR).mpr hsmall
  have hg := hq.trans (min_le_left (1 / (2 * J)) (v / (2 * (oscillationTailConstant n G J + 1))))
  have ht := hq.trans (min_le_right (1 / (2 * J)) (v / (2 * (oscillationTailConstant n G J + 1))))
  have hg' := (le_div_iff₀ (by positivity : 0 < 2 * J)).mp hg
  have ht' := (le_div_iff₀ (by positivity : 0 < 2 * (oscillationTailConstant n G J + 1))).mp ht
  constructor
  · have heq : (r / R) * (2 * J) = (2 * (J * r)) / R := by ring
    rw [heq] at hg'
    simpa only [one_mul] using! (div_le_iff₀ hR).mp hg'
  · have hqpos : 0 < r / R := div_pos hr hR
    nlinarith

theorem DyadicOscillationTests.small_scale_packing_on_top_ball {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (R v : ℝ) (hR : 0 < R) (hv : 0 < v)
    (hcenters : ∀ i ∈ s, dist (F.center i) a ≤ R)
    (hsmall : ∀ i ∈ s, F.radius i ≤ smallRieszRadiusFraction (p + 1) G J v * R)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (hlarge : ∀ i ∈ s, v * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)|) :
    ∑ i ∈ s, F.radius i ^ (p + 1) ≤
      (((4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
        interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2) * G * 3 ^ (p + 1) /
        (v / 2) ^ 2) * R ^ (p + 1) := by
  have hs (i : ι) (hi : i ∈ s) := smallRieszRadiusFraction_bounds (p + 1) G J v
    (F.radius i) R hg.1 hJ (F.radius_pos i) hR (hsmall i hi)
  have hb := F.small_scale_riesz_packing C G hC hg hlower hc hJ s D hRiesz a R (3 * R) v
    hR (by positivity) hv (fun i hi => (hs i hi).1)
    (fun i hi => ball_subset_outer_of_radius_dist (F.center i) a R (3 * R)
      (by linarith [hcenters i hi]))
    (fun i hi => (hs i hi).2) e he hlarge
  have hm : μ.real (ball a (3 * R)) ≤ G * (3 * R) ^ (p + 1) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg (by positivity) _))
      (hg.2 a _ (by positivity))
  have hB : 0 ≤ (4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
      interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2 := by
    unfold interactionPackingConstant
    have hG := hg.1
    positivity
  calc
    _ ≤ _ := hb
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hB) (sq_nonneg (v / 2))
      convert! hh using 1
      rw [mul_pow]
      ring

end

end RieszRectifiability

end OAI
