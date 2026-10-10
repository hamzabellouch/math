import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeMatching
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-!
# Strict cone for a decaying recurrent tail

Decay of the two tail sums, the Laguerre recurrence, and nontriviality beyond
the cutoff give the strict cone inequality in Lemma `free:cone`.
-/

open Filter Topology

namespace DefocusingNLS

/-- Summing the nonnegative cone increments recovers the negative initial
cone. In particular the infinite sum needs no additional summability input. -/
theorem hasSum_cone_increments (p a : ℕ → ℝ) (K : ℕ)
    (hlimit : Tendsto p atTop (𝓝 0))
    (hinc : ∀ n, p (n + 1) - p n = a n)
    (hnonneg : ∀ n, K ≤ n → 0 ≤ a n) :
    HasSum (fun n => a (n + K)) (-p K) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => hnonneg (n + K) (Nat.le_add_left K n)) _).mpr
  have heq (N : ℕ) : ∑ n ∈ Finset.range N, a (n + K) = p (N + K) - p K := by
    simp_rw [← hinc]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.zero_add, Nat.add_zero] using
      Finset.sum_range_sub (fun n => p (n + K)) N
  simp_rw [heq]
  simpa using (hlimit.comp (tendsto_add_atTop_nat K)).sub_const (p K)

/-- Decay of both tail sums makes the cone form tend to zero. -/
theorem coneForm_tendsto_zero (M : ℝ) (s : ℂ) (B C : ℕ → ℂ)
    (hB : Tendsto B atTop (𝓝 0)) (hC : Tendsto C atTop (𝓝 0)) :
    Tendsto (fun n => coneForm M s (B n) (C n)) atTop (𝓝 0) := by
  have hc : Continuous (fun z : ℂ × ℂ => coneForm M s z.1 z.2) := by
    unfold coneForm
    fun_prop
  simpa [coneForm, Function.comp_def] using
    (hc.tendsto (0, 0)).comp (hB.prodMk_nhds hC)

/-- A nontrivial decaying tail satisfying the Laguerre recurrence lies in the
strict cone once the cutoff is at least three. -/
theorem recurrent_tail_cone_negative (σ : ℝ) (ℓ K : ℕ)
    (s : ℂ) (t B C g : ℕ → ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K) (hs : s.re = 0)
    (ht : ∀ n, (t n).re = σ + (ℓ : ℝ) / 2 + n)
    (hrec : ∀ n, t n * g n = -((ℓ : ℝ) + 5 : ℂ) * (B n - g n) - s * C n)
    (hBrec : ∀ n, B (n + 1) = B n - g n)
    (hCrec : ∀ n, C (n + 1) = C n - B (n + 1))
    (hB : Tendsto B atTop (𝓝 0)) (hC : Tendsto C atTop (𝓝 0))
    (hnonzero : ∃ n, K ≤ n ∧ g n ≠ 0) :
    coneForm ((ℓ : ℝ) + 5) s (B K) (C K) < 0 := by
  let p := fun n => coneForm ((ℓ : ℝ) + 5) s (B n) (C n)
  have hinc (n : ℕ) : p (n + 1) - p n =
      (σ + n - 5 / 2) * Complex.normSq (g n) := by
    dsimp [p]
    rw [hCrec, hBrec]
    exact mode_coneForm_increment σ ℓ n s (t n) (B n) (C n) (g n)
      hs (ht n) (hrec n)
  apply negative_of_increasing_tail K (coneForm_tendsto_zero _ _ _ _ hB hC)
  · intro n hn
    have h := mode_increment_nonneg σ n (g n) hσ (hK.trans hn)
    linarith [hinc n]
  · obtain ⟨n, hn, hg⟩ := hnonzero
    refine ⟨n, hn, ?_⟩
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hK.trans hn
    have hpos : 0 < (σ + n - 5 / 2) * Complex.normSq (g n) :=
      mul_pos (by linarith) (Complex.normSq_pos.mpr hg)
    linarith [hinc n]

end DefocusingNLS

end OAI
