import OAI.NumberTheory.Ostmann.QuadraticCenter.CutoffBounds

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def progressionCutoffWeight (N d x : ℝ) (j : ℕ) : ℂ :=
  cutoffFourier (((x + d * (j : ℝ)) / N) ^ 2)

theorem progression_cutoff_variation_le {N d x : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hdN : d ≤ N) (hx : 0 ≤ x) (hxd : x ≤ d) (J : ℕ)
    (hJ : (J : ℝ) ≤ N / d + 1) :
    ‖progressionCutoffWeight N d x J‖ +
      ∑ j ∈ Finset.range J,
        ‖progressionCutoffWeight N d x j - progressionCutoffWeight N d x (j + 1)‖ ≤
      10 * cutoffFourierBound := by
  let u : ℕ → ℝ := fun j => (x + d * (j : ℝ)) / N
  have hu0 (j : ℕ) : 0 ≤ u j := by
    dsimp only [u]
    exact div_nonneg (add_nonneg hx (mul_nonneg hd.le (Nat.cast_nonneg _))) hN.le
  have humono (j : ℕ) : u j ≤ u (j + 1) := by
    dsimp only [u]
    apply div_le_div_of_nonneg_right _ hN.le
    push_cast
    linarith
  have husq (j : ℕ) : (u j) ^ 2 ≤ (u (j + 1)) ^ 2 :=
    pow_le_pow_left₀ (hu0 j) (humono j) 2
  have hpoint (j : ℕ) :
      ‖progressionCutoffWeight N d x j - progressionCutoffWeight N d x (j + 1)‖ ≤
        cutoffFourierBound * ((u (j + 1)) ^ 2 - (u j) ^ 2) := by
    have h := cutoff_fourier_lipschitz ((u j) ^ 2) ((u (j + 1)) ^ 2)
    rw [abs_of_nonpos (sub_nonpos.mpr (husq j))] at h
    convert h using 1 <;> first | rfl | ring
  have htel : ∀ K : ℕ,
      (∑ j ∈ Finset.range K, ((u (j + 1)) ^ 2 - (u j) ^ 2)) = (u K) ^ 2 - (u 0) ^ 2 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ, ih]; ring
  have huJ : u J ≤ 3 := by
    have hm := mul_le_mul_of_nonneg_right hJ hd.le
    have hid : N / d * d = N := div_mul_cancel₀ _ hd.ne'
    dsimp only [u]
    apply (div_le_iff₀ hN).mpr
    nlinarith
  have hsqJ : (u J) ^ 2 - (u 0) ^ 2 ≤ 9 := by
    nlinarith [hu0 J, sq_nonneg (u 0)]
  have hvariation :
      (∑ j ∈ Finset.range J,
        ‖progressionCutoffWeight N d x j - progressionCutoffWeight N d x (j + 1)‖) ≤
      9 * cutoffFourierBound := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, cutoffFourierBound * ((u (j + 1)) ^ 2 - (u j) ^ 2) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = cutoffFourierBound * ((u J) ^ 2 - (u 0) ^ 2) := by rw [← Finset.mul_sum, htel]
      _ ≤ cutoffFourierBound * 9 :=
        mul_le_mul_of_nonneg_left hsqJ cutoffFourierBound_pos.le
      _ = _ := by ring
  have hend := norm_cutoff_fourier_le ((u J) ^ 2)
  change ‖progressionCutoffWeight N d x J‖ ≤ cutoffFourierBound at hend
  linarith

end Ostmann.QuadraticCenter

end

end OAI
