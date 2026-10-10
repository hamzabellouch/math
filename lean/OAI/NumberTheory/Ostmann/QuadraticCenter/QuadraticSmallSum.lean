import OAI.NumberTheory.Ostmann.QuadraticCenter.CenteredQuadraticSum
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSmallSumInterval

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem normalizedSmoothQuadraticSum_l1_bound (P : ℕ) {N : ℝ}
    (hN : 0 < N) (a : ℕ → ℂ) (α : ℝ) :
    ‖normalizedSmoothQuadraticSum P N a α‖ ≤
      N⁻¹ * cutoffFourierBound * ∑ w ∈ cutoffMultiples P N, ‖a w‖ := by
  unfold normalizedSmoothQuadraticSum
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hN.le)]
  calc
    _ ≤ N⁻¹ * ∑ w ∈ cutoffMultiples P N,
        ‖a w * weylPhase (α * (w : ℝ) ^ 2) * cutoffFourier (((w : ℝ) / N) ^ 2)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN.le)
    _ ≤ N⁻¹ * ∑ w ∈ cutoffMultiples P N, ‖a w‖ * cutoffFourierBound := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN.le)
      apply Finset.sum_le_sum
      intro w _
      simp only [norm_mul, weylPhase_norm, mul_one]
      exact mul_le_mul_of_nonneg_left (norm_cutoff_fourier_le _) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem normalized_centered_square_sum_norm_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (c : ZMod (∏ i, p i))
    (P : ℕ) {N : ℝ} (hN : ((∏ i, p i : ℕ) : ℝ) ≤ N) (α : ℝ) :
    ‖normalizedSmoothQuadraticSum P N
      (fun w => centeredProductTransform p hcop S (c * (w : ZMod (∏ i, p i)) ^ 2)) α‖ ≤
      2 * cutoffFourierBound * Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by
  have hd : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Nat.pos_of_neZero (∏ i, p i)
  have hNpos : 0 < N := hd.trans_le hN
  have hcount := centeredProductTransform_square_interval_l1_le p hp hcop S c
    (cutoffMultiples P N) hN (fun w hw => ?_)
  · calc
      _ ≤ N⁻¹ * cutoffFourierBound * ∑ w ∈ cutoffMultiples P N,
          ‖centeredProductTransform p hcop S (c * (w : ZMod (∏ i, p i)) ^ 2)‖ :=
        normalizedSmoothQuadraticSum_l1_bound P hNpos _ α
      _ ≤ N⁻¹ * cutoffFourierBound *
          (2 * N * Real.sqrt ((2 : ℝ) ^ Fintype.card ι)) :=
        mul_le_mul_of_nonneg_left hcount (mul_nonneg (inv_nonneg.mpr hNpos.le)
          cutoffFourierBound_pos.le)
      _ = _ := by field_simp
  · have hw' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hw).1).2
    exact (Nat.cast_le.mpr hw').trans (Nat.floor_le hNpos.le)

theorem centeredQuadraticAmplitude_scalar_square {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i))
    (s v w : ℕ) :
    centeredQuadraticAmplitude p hcop S mInv s v w =
      centeredProductTransform p hcop S
        ((-((s * v : ℕ) : ZMod (∏ i, p i)) * mInv) * (w : ZMod (∏ i, p i)) ^ 2) := by
  unfold centeredQuadraticAmplitude
  congr 1
  push_cast
  ring

theorem centeredQuadraticSum_small_norm_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i))
    (s v P : ℕ) (R h θ : ℝ)
    (hscale : ((∏ i, p i : ℕ) : ℝ) ≤
      Real.sqrt (R / ((s : ℝ) * v / (∏ i, p i : ℕ)))) :
    ‖centeredQuadraticSum p hcop S mInv s v P R h θ‖ ≤
      2 * cutoffFourierBound * Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by
  unfold centeredQuadraticSum
  have ha : centeredQuadraticAmplitude p hcop S mInv s v =
      (fun w : ℕ => centeredProductTransform p hcop S
        ((-((s * v : ℕ) : ZMod (∏ i, p i)) * mInv) * (w : ZMod (∏ i, p i)) ^ 2)) := by
    funext w
    exact centeredQuadraticAmplitude_scalar_square p hcop S mInv s v w
  rw [ha]
  exact normalized_centered_square_sum_norm_le p hp hcop S _ P hscale _

end Ostmann.QuadraticCenter

end

end OAI
