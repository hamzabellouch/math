import OAI.Analysis.LipschitzHilbert.Estimates.ParityPartialSums
import OAI.Analysis.LipschitzHilbert.Fourier.GeneralAnnularVariation

namespace OAI

/-! Spectral support and energy of the even/odd packet subfamilies. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem two_pow_parity (j r : ℕ) :
    (2 : ℝ) ^ (2 * j + r) = 2 ^ r * (4 : ℝ) ^ j := by
  rw [pow_add, pow_mul]
  norm_num
  ring

theorem parityPacket_low {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (a : ℝ) (r : ℕ)
    (hlow : ∀ k ξ, |ξ| < a * (2 : ℝ) ^ k.val → 𝓕 (f k) ξ = 0)
    (j : Fin N) (ξ : ℝ) (hξ : |ξ| < (a * (2 : ℝ) ^ r) * (4 : ℝ) ^ j.val) :
    𝓕 (parityPacket f r j) ξ = 0 := by
  by_cases h : 2 * j.val + r < N
  · simp only [parityPacket, paddedPacket, dite_eq_left h]
    apply hlow ⟨2 * j.val + r,h⟩ ξ
    simpa only [two_pow_parity, mul_assoc] using hξ
  · simp [parityPacket, paddedPacket, h]

theorem parityPacket_high {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (b : ℝ) (r : ℕ)
    (hhigh : ∀ k ξ, b * (2 : ℝ) ^ k.val < |ξ| → 𝓕 (f k) ξ = 0)
    (j : Fin N) (ξ : ℝ) (hξ : (b * (2 : ℝ) ^ r) * (4 : ℝ) ^ j.val < |ξ|) :
    𝓕 (parityPacket f r j) ξ = 0 := by
  by_cases h : 2 * j.val + r < N
  · simp only [parityPacket, paddedPacket, dite_eq_left h]
    apply hhigh ⟨2 * j.val + r,h⟩ ξ
    simpa only [two_pow_parity, mul_assoc] using hξ
  · simp [parityPacket, paddedPacket, h]

theorem sum_parity_le (u : ℕ → ℝ) (N r : ℕ) (hu : ∀ j, 0 ≤ u j)
    (hzero : ∀ j, N ≤ j → u j = 0) :
    (∑ j : Fin N, u (2 * j.val + r)) ≤ ∑ j : Fin N, u j.val := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => 2 * j + r) (Finset.range N) := by
    intro i _ j _ h
    change 2 * i + r = 2 * j + r at h
    omega
  have hmap : (Finset.range N).image (fun j => 2 * j + r) ⊆ Finset.range (2 * N + r + 1) := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hj' := Finset.mem_range.mp hj
    apply Finset.mem_range.mpr
    omega
  have h := Finset.sum_le_sum_of_injOn (fun j : ℕ => 2 * j + r) hinj hmap
    (f := fun j => u (2 * j + r)) (g := u) (fun _ _ => le_rfl) (fun j _ _ => hu j)
  have ht : (∑ j ∈ Finset.range N, u j) = ∑ j ∈ Finset.range (2 * N + r + 1), u j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    exact hzero j (by simpa only [Finset.mem_range, not_lt] using hj)
  rw [← ht] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => u (2 * j + r)) N,
    Fin.sum_univ_eq_sum_range u N]
  exact h

theorem parityPacket_energy {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (r : ℕ) :
    (∑ j, ∫ x, ‖parityPacket f r j x‖ ^ 2) ≤ ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  have h := sum_parity_le (fun j => ∫ x, ‖paddedPacket f j x‖ ^ 2) N r
    (fun j => integral_nonneg (fun x => sq_nonneg _)) (fun j hj => by
      simp [paddedPacket, Nat.not_lt.mpr hj])
  simpa only [parityPacket, paddedPacket, dite_eq_left (Fin.isLt _)] using h

end LipschitzHilbert

end

end OAI
