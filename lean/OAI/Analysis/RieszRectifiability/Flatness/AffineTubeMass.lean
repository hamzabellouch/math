import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Flatness.AffineTubeCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def affineTube {d : ℕ} (S : AffineSubspace ℝ (Ambient d)) (R δ : ℝ) : Set (Ambient d) :=
  closedBall 0 R ∩ {x | infDist x (S : Set (Ambient d)) < δ}

theorem measurableSet_affineTube {d : ℕ} (S : AffineSubspace ℝ (Ambient d)) (R δ : ℝ) :
    MeasurableSet (affineTube S R δ) :=
  measurableSet_closedBall.inter
    (isOpen_lt (continuous_infDist_pt (S : Set (Ambient d))) continuous_const).measurableSet

theorem affineTube_measure_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    μ (affineTube S R δ) ≤
      ENNReal.ofReal (C * (2 * δ) ^ n * (((R + δ / 2) / (δ / 2)) ^ k)) := by
  obtain ⟨c, hcover, hcard⟩ := exists_affine_tube_ball_cover S hS R δ hR hδ
  have hsub : affineTube S R δ ⊆ ⋃ y ∈ c, ball y (2 * δ) := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using! hx.1
    obtain ⟨y, hy, hxy⟩ := hcover x hxR hx.2
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, by simpa only [mem_ball, dist_comm] using! hxy⟩⟩
  have hB : 0 ≤ C * (2 * δ) ^ n := mul_nonneg hg.1 (pow_nonneg (by positivity) n)
  have hbound : μ (affineTube S R δ) ≤ ENNReal.ofReal ((c.card : ℝ) * (C * (2 * δ) ^ n)) := by
    calc
      _ ≤ μ (⋃ y ∈ c, ball y (2 * δ)) := measure_mono hsub
      _ ≤ ∑ y ∈ c, μ (ball y (2 * δ)) := measure_biUnion_finset_le c _
      _ ≤ ∑ _y ∈ c, ENNReal.ofReal (C * (2 * δ) ^ n) := by
        apply Finset.sum_le_sum
        intro y _hy
        exact hg.2 y (2 * δ) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul
          (Nat.cast_nonneg c.card : (0 : ℝ) ≤ c.card), ENNReal.ofReal_natCast]
  have hc : (c.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ k := by
    rw [div_pow]
    exact (le_div_iff₀ (pow_pos (by positivity : 0 < δ / 2) k)).mpr hcard
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_comm] using! mul_le_mul_of_nonneg_right hc hB

theorem affineTube_real_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    μ.real (affineTube S R δ) ≤ C * (2 * δ) ^ n * (((R + δ / 2) / (δ / 2)) ^ k) := by
  have hC := hg.1
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (affineTube_measure_bound μ C hg S hS R δ hR hδ)

theorem lower_dimensional_affineTube_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S) (hkn : k < n)
    (R τ : ℝ) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    μ.real (affineTube S R (τ * R)) ≤
      (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * τ * R ^ n := by
  have hC := hg.1
  have hδ : 0 < τ * R := mul_pos hτ hR
  have hratio : (R + τ * R / 2) / (τ * R / 2) ≤ 3 / τ := by
    have heq : (R + τ * R / 2) / (τ * R / 2) = (2 + τ) / τ := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) hτ.le
  have hpow : τ ^ (n - k) ≤ τ := by
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - k ≠ 0)
    rw [hl, pow_succ]
    simpa only [one_mul] using!
      mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1 : τ ^ l ≤ 1) hτ.le
  have hp : τ ^ n = τ ^ (n - k) * τ ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn.le]
  calc
    _ ≤ C * (2 * (τ * R)) ^ n * (((R + τ * R / 2) / (τ * R / 2)) ^ k) :=
      affineTube_real_bound μ C hg S hS R (τ * R) hR.le hδ
    _ ≤ C * (2 * (τ * R)) ^ n * ((3 / τ) ^ k) := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hratio k)
      positivity
    _ = (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * R ^ n * τ ^ (n - k) := by
      simp only [mul_pow, div_pow, hp]
      field_simp
    _ ≤ (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * R ^ n * τ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
