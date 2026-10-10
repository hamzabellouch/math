import OAI.Geometry.RCD.Harmonic.PinchingTail

namespace OAI

/-! # Removing the affine constants by inward summation -/

open Filter
open scoped Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- A vanishing sequence with the consecutive-fit estimate is bounded by
the square root of the two-sided defect envelope. No summability of the
square roots is assumed. -/
theorem affine_constants_le_envelope {ρ τ C : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 ≤ τ) (hτρ : τ < Real.sqrt ρ) (hC : 0 ≤ C)
    {P c : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ i, |c i - c (i + 1)| ≤
      C * τ ^ i * (Real.sqrt (P i) + Real.sqrt (P (i + 1)))) (i : ℕ) :
    |c i| ≤ C * τ ^ i * (1 - τ / Real.sqrt ρ)⁻¹ *
      (1 + (Real.sqrt ρ)⁻¹) * Real.sqrt (symmetricDefect ρ P i) := by
  obtain ⟨h0, h0b⟩ := geometric_sqrt_tail_le hρ hρ1 hτ hτρ hP hPs i 0
  obtain ⟨h1, h1b⟩ := geometric_sqrt_tail_le hρ hρ1 hτ hτρ hP hPs i 1
  simp only [add_zero, pow_zero, div_one, pow_one] at h0 h0b h1 h1b
  let d : ℕ → ℝ := fun k => C * τ ^ i *
    (τ ^ k * Real.sqrt (P (i + k)) + τ ^ k * Real.sqrt (P (i + 1 + k)))
  have hd : Summable d := (h0.add h1).mul_left (C * τ ^ i)
  have hdist (k : ℕ) : dist (c (i + k)) (c (i + (k + 1))) ≤ d k := by
    have h := hstep (i + k)
    rw [Real.dist_eq]
    convert h using 1
    simp only [d, pow_add]
    ring_nf
  have ht : Tendsto (fun k : ℕ => c (i + k)) atTop (𝓝 0) :=
    hc.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat i)
  have hb := dist_le_tsum_of_dist_le_of_tendsto₀ d hdist hd ht
  simp only [Nat.add_zero, Real.dist_eq, sub_zero] at hb
  have hsum : (∑' k, d k) = C * τ ^ i *
      ((∑' k, τ ^ k * Real.sqrt (P (i + k))) +
        ∑' k, τ ^ k * Real.sqrt (P (i + 1 + k))) := by
    rw [show d = fun k => C * τ ^ i *
      (τ ^ k * Real.sqrt (P (i + k)) + τ ^ k * Real.sqrt (P (i + 1 + k))) from rfl,
      tsum_mul_left, h0.tsum_add h1]
  rw [hsum] at hb
  have hm := mul_le_mul_of_nonneg_left (add_le_add h0b h1b)
    (mul_nonneg hC (pow_nonneg hτ i))
  refine hb.trans (hm.trans_eq ?_)
  ring

end RegularPointCoordinates

end

end OAI
