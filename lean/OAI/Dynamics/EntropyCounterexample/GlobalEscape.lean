import OAI.Dynamics.EntropyCounterexample.PhaseAlignment

namespace OAI

open Filter Set
open scoped Topology
open scoped OnePoint

namespace Problem340.GlobalEscape

theorem tendsto_coe_infty_of_norm {ι E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {l : Filter ι} {z : ι → E}
    (hz : Tendsto (fun n => ‖z n‖) l atTop) :
    Tendsto (fun n => (z n : OnePoint E)) l (𝓝 ∞) := by
  have hc : Tendsto z l (coclosedCompact E) := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp hz
  exact OnePoint.tendsto_coe_infty.comp hc

lemma period_le_of_readout {t : ℝ} {k₀ k : ℤ}
    (hlo : 100 * (k₀ : ℝ) ≤ t) (hhi : t < 100 * (k : ℝ) + 80) :
    k₀ ≤ k := by
  by_contra h
  have hk : k + 1 ≤ k₀ := by omega
  have hkR : (k : ℝ) + 1 ≤ k₀ := by exact_mod_cast hk
  linarith

theorem square_le_after_passage
    (t r : ℕ → ℝ) (ht : Monotone t)
    (hgap : ∀ n, (∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)) → (r n) ^ 2 ≤ r (n + 1))
    (hpass : ∀ k : ℤ, t 0 < 100 * (k : ℝ) →
      ∃ s hi : ℕ, t s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ t hi ∧
        ∀ n, s ≤ n → n < hi → (r n) ^ 2 ≤ r (n + 1))
    {k₀ : ℤ} {N : ℕ} (hstart : t 0 < 100 * (k₀ : ℝ))
    (hN : 100 * (k₀ : ℝ) ≤ t N) :
    ∀ n, N ≤ n → (r n) ^ 2 ≤ r (n + 1) := by
  intro n hn
  by_cases hquiet : ∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)
  · exact hgap n hquiet
  push Not at hquiet
  obtain ⟨k, hklo, hkhi⟩ := hquiet
  have hk : k₀ ≤ k := period_le_of_readout (hN.trans (ht hn)) hkhi
  have hkR : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨s, hi, hs, hhi, hbound⟩ := hpass k (by linarith)
  apply hbound n
  · by_contra h
    have hns : n ≤ s := by omega
    have := ht hns
    linarith
  · by_contra h
    have hhin : hi ≤ n := by omega
    have := ht hhin
    linarith

theorem tendsto_atTop_of_passage_bounds
    (t r : ℕ → ℝ) (ht : Monotone t) (hr : ∀ n, 0 ≤ r n)
    (hgap : ∀ n, (∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)) → (r n) ^ 2 ≤ r (n + 1))
    (hpass : ∀ k : ℤ, t 0 < 100 * (k : ℝ) →
      ∃ s hi : ℕ, t s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ t hi ∧
        ∀ n, s ≤ n → n < hi → (r n) ^ 2 ≤ r (n + 1))
    (hlarge : ∃ k₀ : ℤ, ∃ N : ℕ, t 0 < 100 * (k₀ : ℝ) ∧
      100 * (k₀ : ℝ) ≤ t N ∧ 1 < r N) :
    Tendsto r atTop atTop := by
  obtain ⟨k₀, N, hstart, hN, hrN⟩ := hlarge
  exact Problem340.tendsto_atTop_of_eventually_square_le r N
    (fun n _ => hr n) (square_le_after_passage t r ht hgap hpass hstart hN) hrN

theorem tendsto_atTop_of_complete_passages
    (t r : ℕ → ℝ) (ht : Monotone t) (hr : ∀ n, 0 ≤ r n)
    (hgap : ∀ n, (∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)) → (r n) ^ 2 ≤ r (n + 1))
    (hpass : ∀ k : ℤ, t 0 < 100 * (k : ℝ) →
      ∃ s hi : ℕ, 100 * (k : ℝ) ≤ t s ∧ t s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ t hi ∧
        (∀ n, s ≤ n → n < hi → (r n) ^ 2 ≤ r (n + 1)) ∧
        ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < r j) :
    Tendsto r atTop atTop := by
  apply tendsto_atTop_of_passage_bounds t r ht hr hgap
  · intro k hk
    obtain ⟨s, hi, _, hs, hhi, hsq, _⟩ := hpass k hk
    exact ⟨s, hi, hs, hhi, hsq⟩
  · obtain ⟨k, hk⟩ := exists_int_gt (t 0 / 100)
    have hk' : t 0 < 100 * (k : ℝ) := by linarith
    obtain ⟨s, hi, hs, _, _, _, j, hsj, _, hj⟩ := hpass k hk'
    exact ⟨k, j, hk', hs.trans (ht hsj), hj⟩

end Problem340.GlobalEscape

end OAI
