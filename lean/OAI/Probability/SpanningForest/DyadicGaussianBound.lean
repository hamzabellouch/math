import OAI.Probability.SpanningForest.CountableBrownian
import OAI.Probability.SpanningForest.SchauderTail

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem336.DyadicGaussianBound

variable {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}

theorem ae_time_consistent
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ)) :
    ∀ᵐ ω ∂μ, ∀ i j, τ i = τ j → ω i = ω j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : τ i = τ j
  · have h := CountableBrownian.hasLaw_increment hμ i j
    rw [hij, nndist_self, gaussianReal_zero_var] at h
    filter_upwards [h.ae_eq_of_dirac] with ω hω
    exact fun _ => sub_eq_zero.mp hω
  · exact ae_of_all _ (fun _ h => (hij h).elim)

theorem ae_zero_coordinates
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ)) :
    ∀ᵐ ω ∂μ, ∀ i, τ i = 0 → ω i = 0 := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : τ i = 0
  · have h := CountableBrownian.hasLaw_eval hμ i
    rw [hi, gaussianReal_zero_var] at h
    filter_upwards [h.ae_eq_of_dirac] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ (fun _ h => (hi h).elim)

def sample (τ : ℕ → ℝ≥0) (ω : ℕ → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ i, (τ i : ℝ) = t then ω (Classical.choose h) else 0

@[fun_prop]
theorem measurable_sample (τ : ℕ → ℝ≥0) (t : ℝ) :
    Measurable (fun ω : ℕ → ℝ => sample τ ω t) := by
  classical
  unfold sample
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem sample_time_eq {ω : ℕ → ℝ}
    (hω : ∀ i j, τ i = τ j → ω i = ω j) (i : ℕ) :
    sample τ ω (τ i) = ω i := by
  classical
  unfold sample
  split_ifs with hi
  · apply hω
    exact NNReal.coe_injective (Classical.choose_spec hi)
  · exact (hi ⟨i, rfl⟩).elim

lemma nndist_adjacent_grid (n k : ℕ) :
    nndist (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)
      ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) = (2 : ℝ≥0)⁻¹ ^ n := by
  apply NNReal.coe_injective
  simp only [coe_nndist, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
  change |((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n - (k : ℝ) / (2 : ℝ) ^ n| =
    (2 : ℝ)⁻¹ ^ n
  rw [Nat.cast_add, Nat.cast_one, add_div, add_sub_cancel_left, one_div, inv_pow]
  exact abs_of_nonneg (by positivity)

theorem hasLaw_grid_increment
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
    (idx : ℕ → ℕ → ℕ)
    (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n) (n k : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω (idx n (k + 1)) - ω (idx n k))
      (gaussianReal 0 ((2 : ℝ≥0)⁻¹ ^ n)) μ := by
  have h := CountableBrownian.hasLaw_increment hμ (idx n (k + 1)) (idx n k)
  rwa [hidx, hidx, nndist_adjacent_grid] at h

theorem ae_all_grid_increment_bound
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
    (idx : ℕ → ℕ → ℕ)
    (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n) :
    ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n),
      |ω (idx n (m * 2 ^ n + k.val + 1)) - ω (idx n (m * 2 ^ n + k.val))| ≤
        SchauderTail.incrementRatio ^ n := by
  apply SchauderTail.ae_all_eventually_gaussian_increment_bound (P := μ)
    (fun (m : ℕ) (n : ℕ) (k : Fin (2 ^ n)) (ω : ℕ → ℝ) => ω (idx n (m * 2 ^ n + k.val + 1)) -
      ω (idx n (m * 2 ^ n + k.val)))
  intro m n k
  exact hasLaw_grid_increment hμ idx hidx n (m * 2 ^ n + k.val)

theorem ae_all_sample_increment_bound
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
    (idx : ℕ → ℕ → ℕ)
    (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n) :
    ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n),
      |sample τ ω (((m * 2 ^ n + k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) -
        sample τ ω (((m * 2 ^ n + k.val : ℕ) : ℝ) / (2 : ℝ) ^ n)| ≤
        SchauderTail.incrementRatio ^ n := by
  filter_upwards [ae_time_consistent hμ, ae_all_grid_increment_bound hμ idx hidx]
    with ω hω hbound
  have heval (n k : ℕ) : sample τ ω ((k : ℝ) / (2 : ℝ) ^ n) = ω (idx n k) := by
    have h := sample_time_eq hω (idx n k)
    simpa [hidx, NNReal.coe_div, NNReal.coe_pow] using h
  intro m
  filter_upwards [hbound m] with n hn
  intro k
  simpa only [heval] using hn k

end Problem336.DyadicGaussianBound

end

end OAI
