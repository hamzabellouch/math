import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.FixedCutoffBessel
import OAI.Analysis.RieszRectifiability.Kernel.OriginalTestCutoffError

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem DyadicOscillationTests.small_scale_riesz_packing {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (R T v : ℝ) (hR : 0 < R) (hT : 0 < T) (hv : 0 < v)
    (hsmall : ∀ i ∈ s, 2 * (J * F.radius i) ≤ R)
    (hcontain : ∀ i ∈ s, ball (F.center i) R ⊆ ball a T)
    (htail : ∀ i ∈ s, oscillationTailConstant (p + 1) G J * (F.radius i / R) ≤ v / 2)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (hlarge : ∀ i ∈ s, v * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)|) :
    ∑ i ∈ s, F.radius i ^ (p + 1) ≤
      (((4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
        interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2) * μ.real (ball a T)) /
        (v / 2) ^ 2 := by
  have houter : ∀ i ∈ s, tsupport (F.test i) ⊆ ball a T := by
    intro i hi
    have hr := mul_pos hJ (F.radius_pos i)
    exact (F.support_subset i).trans ((ball_subset_ball (by linarith [hsmall i hi])).trans (hcontain i hi))
  have hcut (i : ι) (hi : i ∈ s) : (v / 2) * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)| := by
    have herr := original_test_outer_cutoff_error p G μ hg (e i) (he i hi) (F.test i)
      (F.lip i) (F.lipschitz i) (F.center i) a (F.radius i) J R T (F.radius_pos i)
      hJ hR (hsmall i hi) (hcontain i hi) (F.lip_bound i) (F.support_subset i) (F.mean_zero i)
    have hb := herr.trans (mul_le_mul_of_nonneg_right (htail i hi)
      (pow_nonneg (F.radius_pos i).le (p + 1)))
    have htri := abs_add_le
      (rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i) -
        rieszScalarPairing (p + 1) (μ.restrict (ball a T))
          (F.center i) (2 * (J * F.radius i)) (e i) (F.test i))
      (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i))
    rw [sub_add_cancel] at htri
    linarith [hlarge i hi]
  have hb := F.fixed_cutoff_bessel C G hC hg hlower hc hJ s D hRiesz a T hT houter e he
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < v / 2))).mpr
  calc
    _ = ∑ i ∈ s, (v / 2) ^ 2 * F.radius i ^ (p + 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ s, (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)) ^ 2 / F.radius i ^ (p + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (le_div_iff₀ (pow_pos (F.radius_pos i) (p + 1))).mpr
      have hs := mul_self_le_mul_self
        (mul_nonneg (by positivity : 0 ≤ v / 2) (pow_nonneg (F.radius_pos i).le _)) (hcut i hi)
      nlinarith [sq_abs (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i))]
    _ ≤ _ := hb

end

end RieszRectifiability

end OAI
