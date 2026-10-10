import OAI.Geometry.RCD.Harmonic.InwardConstantEstimate

namespace OAI

/-! # Removing affine constants in the current covector norm -/

open Filter
open scoped Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- The inward tail is measured in the current radius and current
covector norm. The fixed factor 9/16 combines radius decay and the
proved 9/8 growth of the exact normalizing frames. -/
theorem weighted_affine_constants_le_envelope {ρ C : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτρ : (9 / 16 : ℝ) < Real.sqrt ρ) (hC : 0 ≤ C)
    {P c r w : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P)
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hradius : ∀ i k, r (i + k) = (1 / 2 : ℝ) ^ k * r i)
    (hgrowth : ∀ i k, w (i + k) ≤ (9 / 8 : ℝ) ^ k * w i)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ i, |c i - c (i + 1)| ≤
      C * r i * w i * (Real.sqrt (P i) + Real.sqrt (P (i + 1)))) (i : ℕ) :
    |c i| ≤ C * r i * w i * (1 - (9 / 16 : ℝ) / Real.sqrt ρ)⁻¹ *
      (1 + (Real.sqrt ρ)⁻¹) * Real.sqrt (symmetricDefect ρ P i) := by
  obtain ⟨h0, h0b⟩ := geometric_sqrt_tail_le hρ hρ1 (by norm_num : (0 : ℝ) ≤ 9 / 16) hτρ hP hPs i 0
  obtain ⟨h1, h1b⟩ := geometric_sqrt_tail_le hρ hρ1 (by norm_num : (0 : ℝ) ≤ 9 / 16) hτρ hP hPs i 1
  simp only [add_zero, pow_zero, div_one, pow_one] at h0 h0b h1 h1b
  let d : ℕ → ℝ := fun k => C * r i * w i *
    ((9 / 16 : ℝ) ^ k * Real.sqrt (P (i + k)) +
      (9 / 16 : ℝ) ^ k * Real.sqrt (P (i + 1 + k)))
  have hd : Summable d := (h0.add h1).mul_left (C * r i * w i)
  have hdist (k : ℕ) : dist (c (i + k)) (c (i + (k + 1))) ≤ d k := by
    rw [Real.dist_eq]
    have hs := hstep (i + k)
    rw [hradius i k] at hs
    calc
      _ ≤ C * ((1 / 2 : ℝ) ^ k * r i) * w (i + k) *
          (Real.sqrt (P (i + k)) + Real.sqrt (P (i + k + 1))) := by
        simpa only [Nat.add_assoc] using hs
      _ ≤ C * ((1 / 2 : ℝ) ^ k * r i) * ((9 / 8 : ℝ) ^ k * w i) *
          (Real.sqrt (P (i + k)) + Real.sqrt (P (i + k + 1))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hgrowth i k)
            (mul_nonneg hC (mul_nonneg (pow_nonneg (by norm_num) k) (hr i))))
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = d k := by
        dsimp only [d]
        rw [show (9 / 16 : ℝ) = (1 / 2 : ℝ) * (9 / 8 : ℝ) by norm_num, mul_pow]
        simp only [Nat.add_assoc, Nat.add_comm 1 k]
        ring
  have ht : Tendsto (fun k : ℕ => c (i + k)) atTop (𝓝 0) :=
    hc.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat i)
  have hb := dist_le_tsum_of_dist_le_of_tendsto₀ d hdist hd ht
  simp only [Nat.add_zero, Real.dist_eq, sub_zero] at hb
  have hsum : (∑' k, d k) = C * r i * w i *
      ((∑' k, (9 / 16 : ℝ) ^ k * Real.sqrt (P (i + k))) +
        ∑' k, (9 / 16 : ℝ) ^ k * Real.sqrt (P (i + 1 + k))) := by
    dsimp only [d]
    rw [tsum_mul_left, h0.tsum_add h1]
  rw [hsum] at hb
  have hm := mul_le_mul_of_nonneg_left (add_le_add h0b h1b)
    (mul_nonneg (mul_nonneg hC (hr i)) (hw i))
  refine hb.trans (hm.trans_eq ?_)
  ring

end RegularPointCoordinates

end

end OAI
