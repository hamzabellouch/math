import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.CoarseLevelPacking
import OAI.Analysis.RieszRectifiability.Packing.UniformSmallScalePacking

namespace OAI

/-!
# Packing for Riesz oscillations

The packing constant combines finitely many coarse levels with the small-scale
Riesz packing estimate. Its positivity yields a packing bound whose constant is
chosen uniformly before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def rieszOscillationPackingConstant (n : ℕ) (C G c J v : ℝ) (D : ℝ≥0) (N : ℕ) : ℝ :=
  (N : ℝ) * ((C / c ^ n) * G * (1 + c) ^ n) +
    (((4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
      (D : ℝ) ^ 2) * G * 3 ^ n / (v / 2) ^ 2) + 1

theorem rieszOscillationPackingConstant_pos (n : ℕ) (C G c J v : ℝ) (D : ℝ≥0) (N : ℕ)
    (hC : 0 < C) (hG : 0 ≤ G) (hc : 0 < c) (hJ : 0 < J) :
    0 < rieszOscillationPackingConstant n C G c J v D N := by
  unfold rieszOscillationPackingConstant interactionPackingConstant
  positivity

theorem DyadicOscillationTests.riesz_oscillation_packing {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (R v : ℝ) (hR : 0 < R) (hv : 0 < v) (N : ℕ)
    (hN : (1 / 2 : ℝ) ^ N ≤ smallRieszRadiusFraction (p + 1) G J v)
    (hcenters : ∀ i ∈ s, dist (F.center i) a ≤ R)
    (hradii : ∀ i ∈ s, F.radius i = R * (1 / 2 : ℝ) ^ F.level i)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (hlarge : ∀ i ∈ s, v * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)|) :
    ∑ i ∈ s, F.radius i ^ (p + 1) ≤
      rieszOscillationPackingConstant (p + 1) C G c J v D N * R ^ (p + 1) := by
  classical
  have hcoarse := F.coarse_level_packing C G hC hg hlower hc s N a R hR hcenters (by
    intro i hi
    rw [hradii i hi]
    exact mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num)))
  let t := s.filter (fun i => ¬ F.level i < N)
  have hts (i : ι) (hi : i ∈ t) : i ∈ s := (Finset.mem_filter.mp hi).1
  have hfine := F.small_scale_packing_on_top_ball C G hC hg hlower hc hJ t D hRiesz a R v hR hv
    (fun i hi => hcenters i (hts i hi))
    (by
      intro i hi
      rw [hradii i (hts i hi)]
      have hpow : (1 / 2 : ℝ) ^ F.level i ≤ (1 / 2 : ℝ) ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Nat.le_of_not_gt (Finset.mem_filter.mp hi).2)
      simpa only [mul_comm] using! mul_le_mul_of_nonneg_left (hpow.trans hN) hR.le)
    e (fun i hi => he i (hts i hi)) (fun i hi => hlarge i (hts i hi))
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => F.level i < N)]
  have hsum := add_le_add hcoarse hfine
  dsimp only [t] at hsum
  unfold rieszOscillationPackingConstant
  have hmass : 0 ≤ R ^ (p + 1) := pow_nonneg hR.le _
  nlinarith

theorem exists_uniform_riesz_oscillation_packing_constant (ι : Type*) (p d : ℕ)
    [Nontrivial (Ambient d)] (C G c J v : ℝ) (D : ℝ≥0)
    (hC : 0 < C) (hG : 0 ≤ G) (hc : 0 < c) (hJ : 0 < J) (hv : 0 < v) :
    ∃ B : ℝ, 0 < B ∧ ∀ (μ : Measure (Ambient d)) (_ : SFinite μ),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ ε f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (F : DyadicOscillationTests ι d μ c J) (s : Finset ι) (a : Ambient d) (R : ℝ),
      0 < R → (∀ i ∈ s, dist (F.center i) a ≤ R) →
      (∀ i ∈ s, F.radius i = R * (1 / 2 : ℝ) ^ F.level i) →
      ∀ e : ι → Ambient d, (∀ i ∈ s, ‖e i‖ ≤ 1) →
      (∀ i ∈ s, v * F.radius i ^ (p + 1) ≤
        |rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)|) →
      ∑ i ∈ s, F.radius i ^ (p + 1) ≤ B * R ^ (p + 1) := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (smallRieszRadiusFraction_pos (p + 1) G J v hG hJ hv)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨rieszOscillationPackingConstant (p + 1) C G c J v D N,
    rieszOscillationPackingConstant_pos (p + 1) C G c J v D N hC hG hc hJ, ?_⟩
  intro μ hfinite hg hlower hRiesz F s a R hR hcenters hradii e he hlarge
  let : SFinite μ := hfinite
  exact F.riesz_oscillation_packing C G hC hg hlower hc hJ s D hRiesz a R v hR hv N hN.le
    hcenters hradii e he hlarge

end

end RieszRectifiability

end OAI
